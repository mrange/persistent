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
module Persistent

type PersistentHashMap<'K, 'V when 'K :> System.IEquatable<'K>>  =
  | Empty
  | BitmapN         of uint32*PersistentHashMap<'K, 'V> []
  | KeyValue        of uint32*'K*'V
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

    let inline localHash  h s : uint32 = (h >>> s) &&& TrieMask
    let inline bit        h s : uint32 = 1u <<< int (localHash h s)
    let inline popCount i =
      // From: http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel
      //  x86/x64 support popcnt but that isn't available in ILAsm
      let mutable v = i
      v <- v - ((v >>> 1) &&& 0x55555555u)
      v <- (v &&& 0x33333333u) + ((v >>> 2) &&& 0x33333333u)
      ((v + (v >>> 4) &&& 0xF0F0F0Fu) * 0x1010101u) >>> 24
    let inline localIdx bit b = popCount (b &&& (bit - 1u)) |> int

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
    let rec loop hash shift key m =
      match m with
      | Empty ->
        None
      | BitmapN (b, ns) ->
        let bit = bit hash shift
        if (bit &&& b) <> 0u then
          let localIdx = localIdx bit b
          loop hash (shift + TrieShift) key ns.[localIdx]
        else
          None
      | KeyValue (h, k, v) ->
        if h = hash && equals k key then
          Some v
        else
          None
      | HashCollisionN (h, kvs) ->
        let hloop key i (kvs : _ []) =
          if i < kvs.Length then
            let k, v = kvs.[i]
            if hash = h && equals k key then
              Some v
            else
              None
          else
            None
        if hash = h then
          hloop key 0 kvs
        else
          None
    loop (hashOf key) 0 key m

  let inline set (key : 'K) (value : 'V) (m : PersistentHashMap<'K, 'V>) : PersistentHashMap<'K, 'V> =
    let rec loop hash shift key value m =
      match m with
      | Empty ->
        KeyValue (hash, key, value)
      | BitmapN (b, ns) ->
        let bit = bit hash shift
        let localIdx = localIdx bit b
        if (bit &&& b) <> 0u then
          let nn  = loop hash (shift + TrieShift) key value ns.[localIdx]
          let nns = copyArray ns
          ns.[localIdx] <- nn
          BitmapN (b, nns)
        else
          let nn  = KeyValue (hash, key, value)
          let nns = copyArrayMakeHole localIdx nn ns
          BitmapN (b ||| bit, nns)
      | KeyValue (h, k, v)  ->
        if h = hash && equals k key then
          let kv = KeyValue (hash, key, value)
          kv
        elif h = hash then
          HashCollisionN (hash, [| key, value; k, v |])
        else
          let kv = KeyValue (hash, key, value)
          fromTwoNodes shift hash m h kv
      | HashCollisionN (h, kvs) ->
        if h = hash then
          let nkvs = copyArrayMakeHoleLast (key, value) kvs
          HashCollisionN (h, nkvs)
        else
          let kv = KeyValue (hash, key, value)
          fromTwoNodes shift hash m h kv
    loop (hashOf key) 0 key value m

  let inline visitKeyValues (visitor : 'K -> 'V -> bool) (m : PersistentHashMap<'K, 'V>) : bool =
    let visitor = OptimizedClosures.FSharpFunc<_, _, _>.Adapt visitor
    let rec loop (visitor : OptimizedClosures.FSharpFunc<_, _, _>) m =
      match m with
      | Empty ->
        true
      | BitmapN (b, ns) ->
        let rec nloop (visitor : OptimizedClosures.FSharpFunc<_, _, _>) i (ns : _ []) =
          if i < ns.Length then
            let n = ns.[i]
            if loop visitor n then
              nloop visitor (i + 1) ns
            else
              false
          else
            true
        nloop visitor 0 ns
      | KeyValue (_, k, v) ->
        visitor.Invoke (k, v)
      | HashCollisionN (h, kvs) ->
        let rec hloop (visitor : OptimizedClosures.FSharpFunc<_, _, _>) i (kvs : _ []) =
          if i < kvs.Length then
            let k, v = kvs.[i]
            if visitor.Invoke (k, v) then
              hloop visitor (i + 1) kvs
            else
              false
          else
            true
        hloop visitor 0 kvs
    loop visitor m

  let inline toArray (m : PersistentHashMap<'K, 'V>) : ('K*'V) [] =
    let ra = ResizeArray<_> 16
    visitKeyValues (fun k v -> ra.Add (k, v); true) m |> ignore
    ra.ToArray ()
