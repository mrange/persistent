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

module PropertyTests =
  open FsCheck
  open PHM.CS

  open System
  open System.Collections.Generic

  [<AllowNullLiteral>]
  type Empty () =
    inherit obj ()

  type CopyArrayMakeHoleTestData = CopyArrayMakeHoleTestData of uint32*uint32*Empty []

  module FsLinq =
    open System.Linq

    let inline first    source                        = Enumerable.First    (source)
    let inline groupBy  (selector : 'T -> 'U) source  = Enumerable.GroupBy  (source, Func<'T, 'U> selector)
    let inline last     source                        = Enumerable.Last     (source)
    let inline map      (selector : 'T -> 'U) source  = Enumerable.Select   (source, Func<'T, 'U> selector)
    let inline sortBy   (selector : 'T -> 'U) source  = Enumerable.OrderBy  (source, Func<'T, 'U> selector)
    let inline toArray  source                        = Enumerable.ToArray  (source)

  module Common =
    let notIdentical<'T when 'T : not struct> (f : 'T) (s : 'T) = obj.ReferenceEquals (f, s) |> not

    let check b str =
      if not b then
        printfn "Check failed: %s" str
        failwith str

    let popCount v =
      let rec loop c v =
        if v <> 0u then
          loop (c + 1u) (v &&& (v - 1u))
        else
          c
      loop 0u v

    let copyArrayMakeHole holeBit bitmap (vs : 'T []) =
      check (holeBit <> 0u) "holeBit must bit be 0"
      let nvs       = Array.zeroCreate (vs.Length + 1)
      let mask      = holeBit - 1u
      let lowCount  = popCount (bitmap &&& mask)
      let rec idLoop c i =
        if i < vs.Length then
          if c = 0u then
            skipLoop i
          else
            nvs.[i] <- vs.[i]
            idLoop (c - 1u) (i + 1)
      and skipLoop i =
        if i < vs.Length then
          nvs.[i + 1] <- vs.[i]
          skipLoop (i + 1)
      idLoop lowCount 0
      nvs

    let empty () = PersistentHashMap.Empty<_, _> ()

    let set k v (phm : IPersistentHashMap<_, _>) = phm.Set (k, v)

    let length (phm : IPersistentHashMap<_, _>) = 
      let mutable l = 0
      let visitor _ _ _ = l <- l + 1; true
      phm.Visit (Func<_, _, _, _> visitor) |> ignore
      l

    let uniqueKey vs = 
      vs 
      |> FsLinq.groupBy fst 
      |> FsLinq.map (fun g -> g.Key, (g |> FsLinq.map snd |> FsLinq.last)) 
      |> FsLinq.sortBy fst 
      |> FsLinq.toArray

    let fromArray kvs =
      Array.fold
        (fun s (k, v) -> set k v s)
        (empty ())
        kvs

    let toArray (phm : IPersistentHashMap<'K, 'V>) =
      phm
      |> FsLinq.map (fun kv -> kv.Key, kv.Value)
      |> FsLinq.toArray

    let toSortedKeyArray phm =
      let vs = phm |> toArray
      vs |> Array.sortInPlaceBy fst
      vs

    let checkInvariant (phm : IPersistentHashMap<'K, 'V>) = phm.CheckInvariant ()

  open Common

  type Generators =
    static member CopyArrayMakeHoleData() =
      // TODO: How to shrink
      let g =
        gen {
          let! bitmap = Arb.generate<uint32>
          let bitmap  =
            if bitmap = 0xffffffffu then
              0xfffffffeu // In order to leave a bit free
            else
              bitmap
          let length  = popCount bitmap |> int
          let! vs     = Gen.arrayOfLength length Arb.generate<Empty>
          let! bitpos = Arb.generate<uint32>
          let zbitpos = bitpos % (32u - uint32 length)|> int
          let rec loop bp zbp bmp =
            if zbp = 0 && (bmp &&& 1u) = 0u then
              bp
            elif (bmp &&& 1u) = 0u then
              loop (bp + 1) (zbp - 1) (bmp >>> 1)
            else
              loop (bp + 1) zbp (bmp >>> 1)
          let holeBit = 1u <<< loop 0 zbitpos bitmap
          check (holeBit <> 0u)              "holeBit must not be zero"
          check ((holeBit &&& bitmap) = 0u)  "holeBit must target empty pos in bitmap"
          return CopyArrayMakeHoleTestData (holeBit, bitmap, vs)
        }
      { new Arbitrary<CopyArrayMakeHoleTestData> () with
          member x.Generator  = g
          member x.Shrinker t = Seq.empty
      }

  Arb.register<Generators> () |> ignore

  type ComplexType =
    | IntKey    of  int
    | StringKey of  int
    | TupleKey  of  int*string

  type Action =
    | Add     of int*string
    | Remove  of int

  type Properties () =
    static member ``PopCount returns number of set bits`` (i : uint32) =
      let expected  = popCount i
      let actual    = PersistentHashMap.PopCount i

      expected      = actual

    static member ``CopyArray copies the array`` (vs : int []) =
      let expected  = vs
      let actual    = PersistentHashMap.CopyArray vs

      notIdentical expected actual
      && expected = actual

    static member ``CopyArrayMakeHoleLast copies the array and leaves a hole in last pos`` (vs : Empty []) =
      let expected  = Array.append vs [| null |]
      let actual    = PersistentHashMap.CopyArrayMakeHoleLast vs

      notIdentical expected actual
      && expected = actual

    static member ``CopyArrayMakeHole copies the array and leaves a hole`` (CopyArrayMakeHoleTestData (holeBit, bitmap, vs)) =
      let expected  = copyArrayMakeHole holeBit bitmap vs
      let actual    = PersistentHashMap.CopyArrayMakeHole (holeBit, bitmap, vs)

      notIdentical expected actual
      && expected = actual

    static member ``PHM toArray must contain all added values`` (vs : (int*string) []) =
      let expected  = uniqueKey vs
      let phm       = vs |> fromArray
      let actual    = phm |> toSortedKeyArray

      notIdentical expected actual
      && checkInvariant phm
      && expected = actual

    static member ``PHM TryFind must return all added values`` (vs : (ComplexType*ComplexType) []) =
      let unique    = uniqueKey vs
      let phm       = unique |> fromArray

      let rec loop i =
        if i < unique.Length then
          let k, v = unique.[i]
          match phm.TryFind k with
          | true, fv when fv = v  -> loop (i + 1)
          | _   , _               -> false
        else
          true

      checkInvariant phm
      && loop 0

    static member ``PHM Unset on all added values must yield empty map`` (vs : (ComplexType*Empty) []) =
      let unique    = uniqueKey vs
      let phm       = unique |> fromArray

      let rec loop (phm : IPersistentHashMap<_, _>) i =
        if checkInvariant phm |> not then
          None
        elif i < unique.Length then
          let k, v = unique.[i]
          loop (phm.Unset k) (i + 1)
        else
          Some phm

      match loop phm 0 with
      | Some phm  -> phm.IsEmpty
      | None      -> false

    static member ``PHM should behave as Map`` (vs : Action []) =
      let compare map (phm : IPersistentHashMap<_, _>) =
        let empty =
          match map |> Map.isEmpty, phm.IsEmpty with
          | true  , true
          | false , false -> true
          | _     , _     -> false

        let visitor h k v = 
          match map |> Map.tryFind k with
          | Some fv -> v = fv
          | _       -> false

        checkInvariant phm && (length phm = map.Count) && empty && phm.Visit (Func<_, _, _, _> visitor)

      let ra = ResizeArray<int> ()

      let rec loop map (phm : IPersistentHashMap<_, _>) i =
        if i < vs.Length then
          match vs.[i] with
          | Add (k, v)  ->
            ra.Add k
            let map = map |> Map.add k v
            let phm = phm.Set (k, v)
            compare map phm && loop map phm (i + 1)
          | Remove r    ->
            if ra.Count > 0 then
              let r   = abs r % ra.Count
              let k   = ra.[r]
              ra.RemoveAt r
              let map = map |> Map.remove k
              let phm = phm.Unset k
              compare map phm && loop map phm (i + 1)
            else
              loop map phm (i + 1)
        else
          true

      loop Map.empty (empty ()) 0

  let run () =
#if DEBUG
    let testCount = 100
#else
    let testCount = 1000
#endif

  //  Properties.``PHM TryFind must return all added values`` [|(StringKey -34, TupleKey (0,"")); (IntKey 30, IntKey 0)|] |> printfn "Result: %A"

    let config = { Config.Quick with MaxTest = testCount; MaxFail = testCount }
    Check.All<Properties>  config

module PerformanceTests =
  open PHM.CS

  open System

  // now () returns current time in milliseconds since start
  let now : unit -> int64 =
    let sw = System.Diagnostics.Stopwatch ()
    sw.Start ()
    fun () -> sw.ElapsedMilliseconds

  // time estimates the time 'action' repeated a number of times
  let time repeat action =
    let inline cc i       = System.GC.CollectionCount i

    let v                 = action ()

    System.GC.Collect (2, System.GCCollectionMode.Forced, true)

    let bcc0, bcc1, bcc2  = cc 0, cc 1, cc 2
    let b                 = now ()

    for i in 1..repeat do
      action () |> ignore

    let e = now ()
    let ecc0, ecc1, ecc2  = cc 0, cc 1, cc 2

    v, (e - b), ecc0 - bcc0, ecc1 - bcc1, ecc2 - bcc2

  let makeRandom (seed : int) = 
    let mutable state = int64 seed
    let m = 0x7FFFFFFFL // 2^31 - 1
    let d = 1. / float m
    let a = 48271L      // MINSTD
    let c = 0L
    fun (b : int) (e : int) ->
      state <- (a*state + c) % m
      let r = float state * d
      let v = float (e - b)*r + float b |> int
      v

  type Key(v : int) =
    member x.Value = v

    interface IEquatable<Key> with
      member x.Equals(o : Key)  = v = o.Value

    override x.Equals(o : obj)  =
      match o with
      | :? Key as k -> v = k.Value
      | _           -> false
    override x.GetHashCode()    = v
    override x.ToString()       = sprintf "%d" v

  let random      = makeRandom 19740531
  let total       = 4000000
  let outer       = 40000
  let inner       = total / outer
  let multiplier  = 4
  let inserts     =
    [|
      for i in 0..(inner - 1) -> random 0 (inner*multiplier) |> Key, string i
    |]
  let removals  =
    let a = Array.copy inserts
    for i in 0..(inner - 2) do 
      let s =  random i inner
      let t =  a.[s]
      a.[s] <- a.[i]
      a.[i] <- t
    a

  let length (phm : IPersistentHashMap<_, _>) = 
    let mutable l = 0
    let visitor _ _ _ = l <- l + 1; true
    phm.Visit (Func<_, _, _, _> visitor) |> ignore
    l

  let inline doInsert phm =
    inserts
    |> Array.fold (fun (s : IPersistentHashMap<_, _>) (k, v) -> s.Set (k, v)) phm

  let inline doRemove phm =
    inserts
    |> Array.fold (fun (s : IPersistentHashMap<_, _>) (k, _) -> s.Unset k) phm

  let inline doLookup fa (phm : IPersistentHashMap<_, _>) =
    fa
    |> Array.forall (fun (k, _) -> let r, _ = phm.TryFind k in r)

  let empty     = PersistentHashMap.Empty<Key, string> ()
  let inserted  = doInsert empty

  let insert () =
    let result    = doInsert empty
#if DEBUG
    if length result <> length inserted then
      failwith "Expected to be same length as testSet"
#else
    ()
#endif

  let remove () =
    let result    = doRemove inserted
    if not result.IsEmpty then
      failwith "Expected to be empty"

  let insertAndRemove () =
    let inserted  = doInsert empty
    let result    = doRemove inserted
    if not result.IsEmpty then
      failwith "Expected to be empty"

  let insertAndLookup () =
    let inserted  = doInsert empty
    let result    = doLookup removals inserted
    if not result then
      failwith "Expected true for all"

  let lookupInserted () =
    let result    = doLookup removals inserted
    if not result then
      failwith "Expected true for all"


  let testCases =
    [|
      "Lookup Inserted"     , lookupInserted
      "Insert"              , insert
      "Remove"              , remove
  //    "Insert & Lookup"     , insertAndLookup
  //    "Insert & Remove"     , insertAndRemove
    |]

  let run () =
    for nm, a in testCases do
      printfn "Running test case: %s..." nm
      let _, tm, cc0, cc1, cc2 = time outer a
      printfn "...It took %d ms, CC=%d, %d, %d" tm cc0 cc1 cc2


[<EntryPoint>]
let main argv =
//  PropertyTests.run ()
  PerformanceTests.run ()

  0
