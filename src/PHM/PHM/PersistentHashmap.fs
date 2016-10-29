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

module Persistent

module PersistentHashMapDetails =
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

open PersistentHashMapDetails

type IPersistentHashMap<'K, 'V when 'K :> System.IEquatable<'K>> =
  interface
#if PHM_TEST_BUILD
    abstract CheckInvariant : uint32*int -> bool
#endif
    abstract IsEmpty        : bool
    abstract Set            : uint32*int*KeyValueNode<'K, 'V> -> IPersistentHashMap<'K, 'V>
    abstract TryFind        : uint32*int*'K*(byref<'V>) -> bool
    abstract Unset          : uint32*int*'K -> IPersistentHashMap<'K, 'V>
    abstract Visit          : OptimizedClosures.FSharpFunc<'K, 'V, bool> -> bool
  end
and [<Sealed>] [<AbstractClass>] Common<'K, 'V when 'K :> System.IEquatable<'K>>() =
  static let emptyNode = EmptyNode<'K, 'V> () :> IPersistentHashMap<'K, 'V>

  static member EmptyHashMap = emptyNode

  static member FromTwoNodes shift h1 n1 h2 n2 =
    let b1 = bit h1 shift
    let b2 = bit h2 shift
    if b1 < b2 then
      BitmapNodeN (b1 ||| b2, [| n1; n2 |])
    elif b1 > b2 then
      BitmapNodeN (b2 ||| b1, [| n2; n1 |])
    else
      BitmapNodeN (b1, [| Common<_, _>.FromTwoNodes (shift + TrieShift) h1 n1 h2 n2 |])

and [<Sealed>] EmptyNode<'K, 'V when 'K :> System.IEquatable<'K>>() =
  interface IPersistentHashMap<'K, 'V> with
#if PHM_TEST_BUILD
    member x.CheckInvariant (h, s)  = true
#endif
    member x.IsEmpty                = true
    member x.Set      (h, s, kv)    = upcast kv
    member x.TryFind  (h, s, k, ov) = false
    member x.Unset    (h, s, k)     = upcast x
    member x.Visit    r             = true

and [<Sealed>] KeyValueNode<'K, 'V when 'K :> System.IEquatable<'K>>(hash : uint32, key : 'K, value : 'V) =
  member x.Hash   = hash
  member x.Key    = key
  member x.Value  = value

  interface IPersistentHashMap<'K, 'V> with

#if PHM_TEST_BUILD
    member x.CheckInvariant (h, s)  =
      checkHash hash h s
      && hash = hashOf key
#endif
    member x.IsEmpty                = false
    member x.Set      (h, s, kv)    =
      let k = kv.Key
      if h = hash && equals k key then
        upcast KeyValueNode (h, k, kv.Value)
      elif h = hash then
        upcast HashCollissionNodeN (h, [| x; kv |])
      else
        upcast Common<'K, 'V>.FromTwoNodes s hash x h kv
    member x.TryFind  (h, s, k, ov) =
      if h = hash && equals k key then
        ov <- value
        true
      else
        false
    member x.Unset    (h, s, k)     =
      if h = hash && equals k key then
        Common<'K, 'V>.EmptyHashMap
      else
        upcast x
    member x.Visit  r               = r.Invoke (key, value)

and [<Sealed>] BitmapNodeN<'K, 'V when 'K :> System.IEquatable<'K>>(bitmap : uint32, nodes : IPersistentHashMap<'K, 'V> []) =
#if PHM_TEST_BUILD
  let rec checkInvariantNodes (hash : uint32) shift b localHash i =
    if b <> 0u && i < nodes.Length then
      let n = nodes.[i]
      if (b &&& 1u) = 0u then
        checkInvariantNodes hash shift (b >>> 1) (localHash + 1u) i
      else
        n.CheckInvariant (hash ||| (localHash <<< shift), shift + TrieShift)
        && checkInvariantNodes hash shift (b >>> 1) (localHash + 1u) (i + 1)
    else
      b = 0u
#endif

  let rec visit (r : OptimizedClosures.FSharpFunc<_, _, _>) i =
    if i < nodes.Length then
      let n = nodes.[i]
      n.Visit r
      && visit r (i + 1)
    else
      true

  interface IPersistentHashMap<'K, 'V> with
#if PHM_TEST_BUILD
    member x.CheckInvariant (h, s)  =
      popCount bitmap |> int = nodes.Length
//          && ns.Length > 1
      && checkInvariantNodes h s bitmap 0u 0
#endif
    member x.IsEmpty                = false
    member x.Set      (h, s, kv)    =
      let bit = bit h s
      let localIdx = localIdx bit bitmap
      if (bit &&& bitmap) <> 0u then
        let nn  = nodes.[localIdx].Set (h, s + TrieShift, kv)
        let nns = copyArray nodes
        nns.[localIdx] <- nn
        upcast BitmapNodeN (bitmap, nns)
      else
        let nns = copyArrayMakeHole localIdx (kv :> IPersistentHashMap<'K, 'V>) nodes
        upcast BitmapNodeN (bitmap ||| bit, nns)
    member x.TryFind  (h, s, k, ov) =
      let bit = bit h s
      if (bit &&& bitmap) <> 0u then
        let localIdx = localIdx bit bitmap
        nodes.[localIdx].TryFind (h, s + TrieShift, k, &ov)
      else
        false
    member x.Unset    (h, s, k)     =
      let bit = bit h s
      let localIdx = localIdx bit bitmap
      if (bit &&& bitmap) <> 0u then
        let nn = nodes.[localIdx].Unset (h, s + TrieShift, k)
        if refEqual nn Common<'K, 'V>.EmptyHashMap |> not then
          let nns = copyArray nodes
          nns.[localIdx] <- nn
          upcast BitmapNodeN (bitmap, nns)
        else
          if nodes.Length > 1 then
            let nns = copyArrayRemoveHole localIdx nodes
            upcast BitmapNodeN (bitmap &&& ~~~bit, nns)
          else
            Common<'K, 'V>.EmptyHashMap
      else
        upcast x
    override x.Visit  r             = visit r 0

and [<Sealed>] HashCollissionNodeN<'K, 'V when 'K :> System.IEquatable<'K>>(hash : uint32, keyValues : KeyValueNode<'K, 'V> []) =
#if PHM_TEST_BUILD
  let rec checkInvariant h s i =
    if i < keyValues.Length then
      let kv = keyValues.[i]
      hash = hashOf kv.Key
//      && kv.CheckInvariant (h, s)
      && checkInvariant h s (i + 1)
    else
      true
#endif

  let rec visit (r : OptimizedClosures.FSharpFunc<_, _, _>) i =
    if i < keyValues.Length then
      let kv = keyValues.[i]
      r.Invoke (kv.Key, kv.Value)
      && visit r (i + 1)
    else
      true

  let rec findIndex h k i =
    if i < keyValues.Length then
      let kv = keyValues.[i]
      if h = kv.Hash && equals k kv.Key then
        i
      else
        findIndex h k (i + 1)
    else
      -1

  member x.tryFind (key, i, ov : byref<'V>) =
    if i < keyValues.Length then
      let kv = keyValues.[i]
      if equals kv.Key key then
        ov <- kv.Value
        true
      else
        x.tryFind (key, i + 1, &ov)
    else
      false

  interface IPersistentHashMap<'K, 'V> with
#if PHM_TEST_BUILD
    member x.CheckInvariant (h, s)  =
      checkHash hash h s
      && keyValues.Length > 1
      && checkInvariant h s 0
#endif
    member x.IsEmpty                = false
    member x.Set      (h, s, kv)    =
      if h = hash then
        let nkvs = copyArrayMakeHoleLast kv keyValues
        upcast HashCollissionNodeN (h, nkvs)
      else
        upcast Common<'K, 'V>.FromTwoNodes s hash x h kv
    member x.TryFind  (h, s, k, ov) =
      if h = hash then
        x.tryFind (k, 0, &ov)
      else
        false
    member x.Unset    (h, s, k)     =
      if h = hash then
        let localIdx = findIndex h k 0
        if localIdx > -1 then
          if keyValues.Length > 2 then
            let nkvs = copyArrayRemoveHole localIdx keyValues
            upcast HashCollissionNodeN (hash, nkvs)
          elif keyValues.Length > 1 then
            let kv = keyValues.[localIdx ^^^ 1]
            upcast kv
          else
            Common<'K, 'V>.EmptyHashMap
        else
          upcast x
      else
        upcast x
    override x.Visit  r             = visit r 0

module PersistentHashMap =
  open System

#if PHM_TEST_BUILD
  let checkInvariant (m : IPersistentHashMap<'K, 'V>) : bool =
    m.CheckInvariant (0u, 0)
#endif

  [<GeneralizableValue>]
  let empty<'K, 'V when 'K :> System.IEquatable<'K>> : IPersistentHashMap<_, _> = Common<'K, 'V>.EmptyHashMap

  let inline isEmpty (m : IPersistentHashMap<'K, 'V>) : bool =
    m.IsEmpty

  let inline tryFind (key : 'K) (m : IPersistentHashMap<'K, 'V>) : 'V option =
    let mutable v = Unchecked.defaultof<'V>
    if m.TryFind (hashOf key, 0, key, &v) then
      Some v
    else
      None

  let inline set (key : 'K) (value : 'V) (m : IPersistentHashMap<'K, 'V>) : IPersistentHashMap<'K, 'V> =
    let h   = hashOf key
    let kv  = KeyValueNode (h, key, value)
    m.Set (h, 0, kv)

  let inline unset (key : 'K) (m : IPersistentHashMap<'K, 'V>) : IPersistentHashMap<'K, 'V> =
    let h   = hashOf key
    m.Unset (h, 0, key)

  let inline visit (visitor : 'K -> 'V -> bool) (m : IPersistentHashMap<'K, 'V>) : bool =
    m.Visit (OptimizedClosures.FSharpFunc<_, _, _>.Adapt visitor)

  let inline toArray (m : IPersistentHashMap<'K, 'V>) : ('K*'V) [] =
    let ra = ResizeArray<_> 16
    visit (fun k v -> ra.Add (k, v); true) m |> ignore
    ra.ToArray ()

  let inline length (m : IPersistentHashMap<'K, 'V>) : int =
    let l = ref 0
    visit (fun k v -> incr l; true) m |> ignore
    !l

