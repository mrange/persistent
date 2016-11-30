// ----------------------------------------------------------------------------------------------
// Copyright 2016 Mårten Rånge
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// ----------------------------------------------------------------------------------------------

// Inspired by Clojure's Persistent Hash Map (https://github.com/clojure/clojure/blob/master/src/jvm/clojure/lang/PersistentHashMap.java)
//  and Phil Bagwell's Ideal Hash Trie (http://lampwww.epfl.ch/papers/idealhashtrees.pdf)
//  and http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel

namespace Persistent

module Details = 
  open System
  [<Literal>]
  let TrieShift     = 4
  [<Literal>]
  let TrieMaxShift  = 32
  [<Literal>]
  let TrieMaxNodes  = 16  // 1 <<< downshift
  [<Literal>]
  let TrieMask      = 15u // maxNodes - 1

  let inline localHash  h s = (h >>> s) &&& TrieMask
  let inline bit        h s = 1u <<< int (localHash h s)
  let inline popCount   i   =
    // From: http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel
    //  x86/x64 support popcnt but that isn't available in ILAsm
    let mutable v = i
    v <- v - ((v >>> 1) &&& 0x55555555u)
    v <- (v &&& 0x33333333u) + ((v >>> 2) &&& 0x33333333u)
    ((v + (v >>> 4) &&& 0xF0F0F0Fu) * 0x1010101u) >>> 24
  let inline localIdx bit b = popCount (b &&& (bit - 1u)) |> int
  let inline checkHash hash localHash shift = (hash &&& ((1u <<< shift) - 1u)) = localHash

  let inline refEqual<'T when 'T: not struct> (l : 'T) (r : 'T) = Object.ReferenceEquals (l, r)

  let inline copyArray (vs : 'T []) : 'T [] =
    let nvs = Array.zeroCreate vs.Length
    System.Array.Copy (vs, nvs, vs.Length)
    nvs

  let inline copyArrayMakeHoleLast (peg : 'T) (vs : 'T []) : 'T [] =
    let nvs = Array.zeroCreate (vs.Length + 1)
    System.Array.Copy (vs, nvs, vs.Length)
    nvs.[vs.Length] <- peg
    nvs

  let inline copyArrayMakeHole (at : int) (peg : 'T) (vs : 'T []) : 'T [] =
    let nvs = Array.zeroCreate (vs.Length + 1)
    System.Array.Copy (vs, nvs, at)
    System.Array.Copy (vs, at, nvs, at + 1, vs.Length - at)
    nvs.[at] <- peg
    nvs

  let inline copyArrayRemoveHole (at : int) (vs : 'T []) : 'T [] =
    let nvs = Array.zeroCreate (vs.Length - 1)
    System.Array.Copy (vs, nvs, at)
    System.Array.Copy (vs, at + 1, nvs, at, vs.Length - at - 1)
    nvs

  // TODO: boxing seems optimized away, verify
  let inline hashOf<'T when 'T :> IEquatable<'T>> (v : 'T)           = (box v).GetHashCode () |> uint32
  let inline equals<'T when 'T :> IEquatable<'T>> (l : 'T) (r : 'T)  = l.Equals r

open Details

type [<AbstractClass>] PersistentHashMap<'K, 'V when 'K :> System.IEquatable<'K>>() =
  static let emptyNode = EmptyNode<'K, 'V> () :> PersistentHashMap<'K, 'V>

#if PHM_TEST_BUILD
  abstract DoCheckInvariant : uint32  -> int  -> bool
#endif
  abstract DoIsEmpty        : unit    -> bool
  abstract DoVisit          : OptimizedClosures.FSharpFunc<'K, 'V, bool> -> bool
  abstract DoSet            : uint32  -> int  -> KeyValueNode<'K, 'V> -> PersistentHashMap<'K, 'V>
  abstract DoTryFind        : uint32*int*'K*byref<'V> -> bool
  abstract DoUnset          : uint32  -> int  -> 'K -> PersistentHashMap<'K, 'V>

  default  x.DoIsEmpty ()   = false

#if PHM_TEST_BUILD
  member x.CheckInvariant () = x.DoCheckInvariant 0u 0
#endif
  member x.IsEmpty    = x.DoIsEmpty ()
  member x.Visit   r  = x.DoVisit (OptimizedClosures.FSharpFunc<_, _, _>.Adapt r)
  member x.Set     k v=
    let h = hashOf k
    x.DoSet h 0 (KeyValueNode (h, k, v))
  member x.TryFind (k, rv : byref<'V>) =
    rv <- Unchecked.defaultof<'V>
    let h = hashOf k
    x.DoTryFind (h, 0, k, &rv)
  member x.Unset   k  =
    let h = hashOf k
    x.DoUnset h 0 k

  static member internal Empty = emptyNode

  static member internal FromTwoNodes shift h1 n1 h2 n2 : PersistentHashMap<_, _> =
    let b1 = bit h1 shift
    let b2 = bit h2 shift
    if b1 < b2 then
      upcast BitmapNodeN (b1 ||| b2, [| n1; n2 |])
    elif b1 > b2 then
      upcast BitmapNodeN (b2 ||| b1, [| n2; n1 |])
    else
      upcast BitmapNode1 (b1, PersistentHashMap<_, _>.FromTwoNodes (shift + TrieShift) h1 n1 h2 n2)

and [<Sealed>] internal EmptyNode<'K, 'V when 'K :> System.IEquatable<'K>>() =
  inherit PersistentHashMap<'K, 'V>()

#if PHM_TEST_BUILD
  override x.DoCheckInvariant h s = true
#endif
  override x.DoVisit    r             = true
  override x.DoIsEmpty  ()            = true
  override x.DoSet      h s kv        = upcast kv
  override x.DoTryFind  (h, s, k, rv) = false
  override x.DoUnset    h s k         = PersistentHashMap<'K, 'V>.Empty

and [<Sealed>] KeyValueNode<'K, 'V when 'K :> System.IEquatable<'K>>(hash : uint32, key : 'K, value : 'V) =
  inherit PersistentHashMap<'K, 'V>()

  member x.Hash   = hash
  member x.Key    = key
  member x.Value  = value

#if PHM_TEST_BUILD
  override x.DoCheckInvariant h s =
    checkHash hash h s
    && hash = hashOf key
#endif
  override x.DoVisit    r           = r.Invoke (key, value)
  override x.DoSet      h s kv      =
    let k = kv.Key
    if h = hash && equals k key then
      upcast KeyValueNode (h, k, kv.Value)
    elif h = hash then
      upcast HashCollisionNodeN (h, [| x; kv |])
    else
      PersistentHashMap<'K, 'V>.FromTwoNodes s hash x h kv
  override x.DoTryFind  (h, s, k, rv) =
    if h = hash && equals k key then
      rv <- value
      true
    else
      false
  override x.DoUnset    h s k       =
    if h = hash && equals k key then
      PersistentHashMap<'K, 'V>.Empty
    else
      upcast x

and [<Sealed>] internal BitmapNode1<'K, 'V when 'K :> System.IEquatable<'K>>(bitmap : uint32, node : PersistentHashMap<'K, 'V>) =
  inherit PersistentHashMap<'K, 'V>()

#if PHM_TEST_BUILD
  override x.DoCheckInvariant h s =
    let localIdx = popCount (bitmap - 1u)
    popCount bitmap |> int = 1
    && node.DoCheckInvariant (h ||| (localIdx <<< s)) (s + TrieShift)
#endif
  override x.DoVisit    r           = node.DoVisit r
  override x.DoSet      h s kv      =
    let bit = bit h s
    if (bit &&& bitmap) <> 0u then
      let nn  = node.DoSet h (s + TrieShift) kv
      upcast BitmapNode1 (bitmap, nn)
    elif bitmap < bit then
      upcast BitmapNodeN (bitmap ||| bit, [| node; kv |])
    else
      upcast BitmapNodeN (bit ||| bitmap, [| kv; node |])

  override x.DoTryFind (h, s, k, rv) =
    let bit = bit h s
    if (bit &&& bitmap) <> 0u then
      node.DoTryFind (h, (s + TrieShift), k, &rv)
    else
      false
  override x.DoUnset    h s k       =
    let bit = bit h s
    if (bit &&& bitmap) <> 0u then
      let nn = node.DoUnset h (s + TrieShift) k
      if refEqual nn PersistentHashMap<'K, 'V>.Empty |> not then
        upcast BitmapNode1 (bitmap, nn)
      else
        PersistentHashMap<'K, 'V>.Empty
    else
      upcast x

and [<Sealed>] internal BitmapNodeN<'K, 'V when 'K :> System.IEquatable<'K>>(bitmap : uint32, nodes : PersistentHashMap<'K, 'V> []) =
  inherit PersistentHashMap<'K, 'V>()

#if PHM_TEST_BUILD
  let rec doCheckInvariantNodes (hash : uint32) shift b localHash i =
    if b <> 0u && i < nodes.Length then
      let n = nodes.[i]
      if (b &&& 1u) = 0u then
        doCheckInvariantNodes hash shift (b >>> 1) (localHash + 1u) i
      else
        n.DoCheckInvariant (hash ||| (localHash <<< shift)) (shift + TrieShift)
        && doCheckInvariantNodes hash shift (b >>> 1) (localHash + 1u) (i + 1)
    else
      b = 0u
#endif

  let rec doVisit (r : OptimizedClosures.FSharpFunc<_, _, _>) i =
    if i < nodes.Length then
      let n = nodes.[i]
      n.DoVisit r
      && doVisit r (i + 1)
    else
      true

#if PHM_TEST_BUILD
  override x.DoCheckInvariant h s =
    popCount bitmap |> int = nodes.Length
//          && ns.Length > 1
    && doCheckInvariantNodes h s bitmap 0u 0
#endif
  override x.DoVisit    r           = doVisit r 0
  override x.DoSet      h s kv      =
    let bit = bit h s
    let localIdx = localIdx bit bitmap
    if (bit &&& bitmap) <> 0u then
      let nn  = nodes.[localIdx].DoSet h (s + TrieShift) kv
      let nns = copyArray nodes
      nns.[localIdx] <- nn
      upcast BitmapNodeN (bitmap, nns)
    else
      let nns = copyArrayMakeHole localIdx (kv :> PersistentHashMap<'K, 'V>) nodes
      if nns.Length < 16 then
        upcast BitmapNodeN (bitmap ||| bit, nns)
      else
        upcast BitmapNode16 nns
  override x.DoTryFind (h, s, k, rv)=
    let bit = bit h s
    if (bit &&& bitmap) <> 0u then
      let localIdx = localIdx bit bitmap
      nodes.[localIdx].DoTryFind (h, (s + TrieShift), k, &rv)
    else
      false
  override x.DoUnset    h s k       =
    let bit = bit h s
    let localIdx = localIdx bit bitmap
    if (bit &&& bitmap) <> 0u then
      let nn = nodes.[localIdx].DoUnset h (s + TrieShift) k
      if refEqual nn PersistentHashMap<'K, 'V>.Empty |> not then
        let nns = copyArray nodes
        nns.[localIdx] <- nn
        upcast BitmapNodeN (bitmap, nns)
      else
        if nodes.Length > 2 then
          let nns = copyArrayRemoveHole localIdx nodes
          upcast BitmapNodeN (bitmap &&& ~~~bit, nns)
        elif nodes.Length > 1 then
          upcast BitmapNode1 (bitmap &&& ~~~bit, nodes.[1 - localIdx])
        else
          PersistentHashMap<'K, 'V>.Empty
    else
      upcast x

and [<Sealed>] internal BitmapNode16<'K, 'V when 'K :> System.IEquatable<'K>>(nodes : PersistentHashMap<'K, 'V> []) =
  inherit PersistentHashMap<'K, 'V>()

#if PHM_TEST_BUILD
  let rec doCheckInvariantNodes (hash : uint32) shift localHash i =
    if i < nodes.Length then
      let n = nodes.[i]
      n.DoCheckInvariant (hash ||| (localHash <<< shift)) (shift + TrieShift)
      && doCheckInvariantNodes hash shift (localHash + 1u) (i + 1)
    else
      true
#endif

  let rec doVisit (r : OptimizedClosures.FSharpFunc<_, _, _>) i =
    if i < nodes.Length then
      let n = nodes.[i]
      n.DoVisit r
      && doVisit r (i + 1)
    else
      true

#if PHM_TEST_BUILD
  override x.DoCheckInvariant h s =
//          && ns.Length > 1
    doCheckInvariantNodes h s 0u 0
#endif
  override x.DoVisit    r           = doVisit r 0
  override x.DoSet      h s kv      =
    let localIdx = localHash h s |> int
    let nn  = nodes.[localIdx].DoSet h (s + TrieShift) kv
    let nns = copyArray nodes
    nns.[localIdx] <- nn
    upcast BitmapNode16 (nns)
  override x.DoTryFind (h, s, k, rv)=
    let localIdx = localHash h s |> int
    nodes.[localIdx].DoTryFind (h, (s + TrieShift), k, &rv)
  override x.DoUnset    h s k       =
    let bit       = bit h s
    let localIdx  = localHash h s |> int
    let nn = nodes.[localIdx].DoUnset h (s + TrieShift) k
    if refEqual nn PersistentHashMap<'K, 'V>.Empty |> not then
      let nns = copyArray nodes
      nns.[localIdx] <- nn
      upcast BitmapNode16 (nns)
    else
      let nns = copyArrayRemoveHole localIdx nodes
      upcast BitmapNodeN (TrieMask &&& ~~~bit, nns)

and [<Sealed>] internal HashCollisionNodeN<'K, 'V when 'K :> System.IEquatable<'K>>(hash : uint32, keyValues : KeyValueNode<'K, 'V> []) =
  inherit PersistentHashMap<'K, 'V>()

#if PHM_TEST_BUILD
  let rec doCheckInvariant h s i =
    if i < keyValues.Length then
      let kv = keyValues.[i]
      hash = hashOf kv.Key
      && kv.DoCheckInvariant h s
      && doCheckInvariant h s (i + 1)
    else
      true
#endif

  let rec doVisit (r : OptimizedClosures.FSharpFunc<_, _, _>) i =
    if i < keyValues.Length then
      let kv = keyValues.[i]
      r.Invoke (kv.Key, kv.Value)
      && doVisit r (i + 1)
    else
      true

  let rec tryFind key i =
    if i < keyValues.Length then
      let kv = keyValues.[i]
      if equals kv.Key key then
        i
      else
        tryFind key (i + 1)
    else
      -1

  let rec findIndex h k i =
    if i < keyValues.Length then
      let kv = keyValues.[i]
      if h = kv.Hash && equals k kv.Key then
        i
      else
        findIndex h k (i + 1)
    else
      -1

#if PHM_TEST_BUILD
  override x.DoCheckInvariant h s =
    checkHash hash h s
    && keyValues.Length > 1
    && doCheckInvariant h s 0
#endif
  override x.DoVisit    r           = doVisit r 0
  override x.DoSet      h s kv      =
    if h = hash then
      let nkvs = copyArrayMakeHoleLast kv keyValues
      upcast HashCollisionNodeN (h, nkvs)
    else
      PersistentHashMap<'K, 'V>.FromTwoNodes s hash x h kv
  override x.DoTryFind (h, s, k, rv)=
    if h = hash then
      let i = tryFind k 0
      if i > -1 then
        rv <- keyValues.[i].Value
        true
      else
        false
    else
      false
  override x.DoUnset    h s k       =
    if h = hash then
      let localIdx = findIndex h k 0
      if localIdx > -1 then
        if keyValues.Length > 2 then
          let nkvs = copyArrayRemoveHole localIdx keyValues
          upcast HashCollisionNodeN (hash, nkvs)
        elif keyValues.Length > 1 then
          let kv = keyValues.[localIdx ^^^ 1]
          upcast kv
        else
          PersistentHashMap<'K, 'V>.Empty
      else
        upcast x
    else
      upcast x

