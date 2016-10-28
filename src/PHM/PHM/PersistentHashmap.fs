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

type PersistentHashMap<'K, 'V when 'K :> System.IEquatable<'K>>  =
  | BitmapN         of uint32*PersistentHashMap<'K, 'V> []
  | KeyValue        of uint32*'K*'V
  | Empty
  | HashCollisionN  of uint32*('K*'V) []

module PersistentHashMap =
  open System

  module Details =
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

    let rec fromTwoNodes shift h1 n1 h2 n2 =
      let b1 = bit h1 shift
      let b2 = bit h2 shift
      if b1 < b2 then
        BitmapN (b1 ||| b2, [| n1; n2 |])
      elif b1 > b2 then
        BitmapN (b2 ||| b1, [| n2; n1 |])
      else
        BitmapN (b1, [| fromTwoNodes (shift + TrieShift) h1 n1 h2 n2 |])

    // TODO: boxing seems optimized away, verify
    let inline hashOf<'T when 'T :> IEquatable<'T>> (v : 'T)           = (box v).GetHashCode () |> uint32
    let inline equals<'T when 'T :> IEquatable<'T>> (l : 'T) (r : 'T)  = l.Equals r

    module Loops =
      let rec tryFindKeyValues key i (kvs : _ []) =
        if i < kvs.Length then
          let k, v = kvs.[i]
          if equals k key then
            Some v
          else
            tryFindKeyValues key (i + 1) kvs
        else
          None

      let rec tryFind hash shift key m =
        match m with
        | BitmapN (b, ns) ->
          let bit = bit hash shift
          if (bit &&& b) <> 0u then
            let localIdx = localIdx bit b
            tryFind hash (shift + TrieShift) key ns.[localIdx]
          else
            None
        | KeyValue (h, k, v) ->
          if h = hash && equals k key then
            Some v
          else
            None
        | Empty ->
          None
        | HashCollisionN (h, kvs) ->
          if hash = h then
            tryFindKeyValues key 0 kvs
          else
            None

      let rec set hash shift key value m =
        match m with
        | BitmapN (b, ns) ->
          let bit = bit hash shift
          let localIdx = localIdx bit b
          if (bit &&& b) <> 0u then
            let nn  = set hash (shift + TrieShift) key value ns.[localIdx]
            let nns = copyArray ns
            nns.[localIdx] <- nn
            BitmapN (b, nns)
          else
            let nn  = KeyValue (hash, key, value)
            let nns = copyArrayMakeHole localIdx nn ns
            BitmapN (b ||| bit, nns)
        | KeyValue (h, k, v) ->
          if h = hash && equals k key then
            KeyValue (hash, key, value)
          elif h = hash then
            HashCollisionN (hash, [| key, value; k, v |])
          else
            let kv = KeyValue (hash, key, value)
            fromTwoNodes shift h m hash kv
        | Empty ->
          KeyValue (hash, key, value)
        | HashCollisionN (h, kvs) ->
          if h = hash then
            let nkvs = copyArrayMakeHoleLast (key, value) kvs
            HashCollisionN (h, nkvs)
          else
            let kv = KeyValue (hash, key, value)
            fromTwoNodes shift h m hash kv

      let rec findKeyValueIndex key i (kvs : _ []) =
        if i < kvs.Length then
          let k, _ = kvs.[i]
          if equals k key then
            i
          else
            findKeyValueIndex key (i + 1) kvs
        else
          -1

      let rec unset hash shift key m =
        match m with
        | BitmapN (b, ns) ->
          let bit = bit hash shift
          let localIdx = localIdx bit b
          if (bit &&& b) <> 0u then
            let nn  = unset hash (shift + TrieShift) key ns.[localIdx]
            match nn with
            | Empty ->
              if ns.Length > 1 then
                let nns = copyArrayRemoveHole localIdx ns
                BitmapN (b &&& ~~~bit, nns)
              else
                Empty
            | _     ->
              let nns = copyArray ns
              nns.[localIdx] <- nn
              BitmapN (b, nns)
          else
            m
        | KeyValue (h, k, v) ->
          if h = hash && equals k key then
            Empty
          else
            m
        | Empty ->
          Empty
        | HashCollisionN (h, kvs) ->
          if h = hash then
            let localIdx = findKeyValueIndex key 0 kvs
            if localIdx > -1 then
              if kvs.Length > 2 then
                let nkvs = copyArrayRemoveHole localIdx kvs
                HashCollisionN (h, nkvs)
              elif kvs.Length > 1 then
                let k, v = kvs.[localIdx ^^^ 1]
                KeyValue (h, k , v)
              else
                Empty
            else
              m
          else
            m

      let rec visitKeyValuesKeyValues (visitor : OptimizedClosures.FSharpFunc<_, _, _>) i (kvs : _ []) =
        if i < kvs.Length then
          let k, v = kvs.[i]
          visitor.Invoke (k, v)
          && visitKeyValuesKeyValues visitor (i + 1) kvs
        else
          true

      let rec visitKeyValuesNodes (visitor : OptimizedClosures.FSharpFunc<_, _, _>) i (ns : _ []) =
        if i < ns.Length then
          let n = ns.[i]
          visitKeyValues visitor n
          && visitKeyValuesNodes visitor (i + 1) ns
        else
          true

      and visitKeyValues (visitor : OptimizedClosures.FSharpFunc<_, _, _>) m =
        match m with
        | BitmapN (b, ns) ->
          visitKeyValuesNodes visitor 0 ns
        | KeyValue (_, k, v) ->
          visitor.Invoke (k, v)
        | Empty ->
          true
        | HashCollisionN (h, kvs) ->
          visitKeyValuesKeyValues visitor 0 kvs

      let rec checkInvariantKeyValues h i (kvs : _ []) =
        if i < kvs.Length then
          let k, v = kvs.[i]
          h = hashOf k
          && checkInvariantKeyValues h (i + 1) kvs
        else
          true

      let rec checkInvariantNodes (hash : uint32) shift b localHash i (ns : _ []) =
        if b <> 0u && i < ns.Length then
          let n = ns.[i]
          if (b &&& 1u) = 0u then
            checkInvariantNodes hash shift (b >>> 1) (localHash + 1u) i ns
          else
            checkInvariant (hash ||| (localHash <<< shift)) (shift + TrieShift) n
            && checkInvariantNodes hash shift (b >>> 1) (localHash + 1u) (i + 1) ns
        else
          b = 0u

      and checkInvariant hash shift m =
        match m with
        | BitmapN (b, ns) ->
          popCount b |> int = ns.Length
//          && ns.Length > 1
          && checkInvariantNodes hash shift b 0u 0 ns
        | KeyValue (h, k, v) ->
          checkHash h hash shift
          && h = hashOf k
        | Empty ->
          true
        | HashCollisionN (h, kvs) ->
          checkHash h hash shift
          && kvs.Length > 1
          && checkInvariantKeyValues h 0 kvs

  open Details

  [<GeneralizableValue>]
  let empty = Empty

  let inline isEmpty (m : PersistentHashMap<'K, 'V>) : bool =
    match m with
    | Empty ->
      true
    | _ ->
      false

  let inline tryFind (key : 'K) (m : PersistentHashMap<'K, 'V>) : 'V option =
    Loops.tryFind (hashOf key) 0 key m

  let inline set (key : 'K) (value : 'V) (m : PersistentHashMap<'K, 'V>) : PersistentHashMap<'K, 'V> =
    Loops.set (hashOf key) 0 key value m

  let inline unset (key : 'K) (m : PersistentHashMap<'K, 'V>) : PersistentHashMap<'K, 'V> =
    Loops.unset (hashOf key) 0 key m

  let inline visitKeyValues (visitor : 'K -> 'V -> bool) (m : PersistentHashMap<'K, 'V>) : bool =
    let visitor = OptimizedClosures.FSharpFunc<_, _, _>.Adapt visitor
    Loops.visitKeyValues visitor m

  let inline toArray (m : PersistentHashMap<'K, 'V>) : ('K*'V) [] =
    let ra = ResizeArray<_> 16
    visitKeyValues (fun k v -> ra.Add (k, v); true) m |> ignore
    ra.ToArray ()

  let inline length (m : PersistentHashMap<'K, 'V>) : int =
    let mutable l = 0
    visitKeyValues (fun k v -> l <- l + 1; true) m |> ignore
    l

  let checkInvariant (phm : PersistentHashMap<'K, 'V>) : bool =
    Loops.checkInvariant 0u 0 phm

