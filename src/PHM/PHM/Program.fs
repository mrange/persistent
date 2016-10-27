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
  open Persistent
  open System

  module FsLinq =
    open System.Linq

    let inline first    source                        = Enumerable.First    (source)
    let inline groupBy  (selector : 'T -> 'U) source  = Enumerable.GroupBy  (source, Func<'T, 'U> selector)
    let inline last     source                        = Enumerable.Last     (source)
    let inline map      (selector : 'T -> 'U) source  = Enumerable.Select   (source, Func<'T, 'U> selector)
    let inline sortBy   (selector : 'T -> 'U) source  = Enumerable.OrderBy  (source, Func<'T, 'U> selector)
    let inline toArray  source                        = Enumerable.ToArray  (source)

  let uniqueKey vs =
    vs
    |> FsLinq.groupBy fst
    |> FsLinq.map (fun g -> g.Key, (g |> FsLinq.map snd |> FsLinq.last))
    |> FsLinq.sortBy fst
    |> FsLinq.toArray

  let fromArray kvs =
    Array.fold
      (fun s (k, v) -> PersistentHashMap.set k v s)
      PersistentHashMap.empty
      kvs

  let toArray phm =
    phm
    |> PersistentHashMap.toArray

  let toSortedKeyArray phm =
    let vs = phm |> toArray
    vs |> Array.sortInPlaceBy fst
    vs

  let notIdentical<'T when 'T : not struct> (f : 'T) (s : 'T) = obj.ReferenceEquals (f, s) |> not

  type ComplexType =
    | IntKey    of  int
    | StringKey of  int
    | TupleKey  of  int*string

  type HalfHash(v : int) =
    member x.Value = v

    interface IComparable<HalfHash> with
      member x.CompareTo(o : HalfHash)  = v.CompareTo o.Value

    interface IEquatable<HalfHash> with
      member x.Equals(o : HalfHash)  = v = o.Value

    override x.Equals(o : obj)  =
      match o with
      | :? HalfHash as k -> v = k.Value
      | _                -> false
    override x.GetHashCode()    = (v.GetHashCode ()) >>> 16 // In order to get a fair bunch of duplicated hashes
    override x.ToString()       = sprintf "%d" v

  type Action =
    | Add     of int*string
    | Remove  of int

  type Properties () =
    static member ``PHM toArray must contain all added values`` (vs : (int*string) []) =
      let expected  = uniqueKey vs
      let phm       = vs |> fromArray
      let actual    = phm |> toSortedKeyArray

      notIdentical expected actual
      && PersistentHashMap.checkInvariant phm
      && expected = actual

    static member ``PHM TryFind must return all added values`` (vs : (ComplexType*ComplexType) []) =
      let unique    = uniqueKey vs
      let phm       = unique |> fromArray

      let rec loop i =
        if i < unique.Length then
          let k, v = unique.[i]
          match PersistentHashMap.tryFind k phm with
          | Some fv when fv = v -> loop (i + 1)
          | _                   -> false
        else
          true

      PersistentHashMap.checkInvariant phm
      && loop 0

    static member ``PHM Unset on all added values must yield empty map`` (vs : (HalfHash*int) []) =
      let unique    = uniqueKey vs
      let phm       = unique |> fromArray

      let rec loop (phm : PersistentHashMap<_, _>) i =
        if PersistentHashMap.checkInvariant phm |> not then
          None
        elif i < unique.Length then
          if phm |> PersistentHashMap.isEmpty then
            None
          else
            let k, v = unique.[i]
            loop (PersistentHashMap.unset k phm) (i + 1)
        else
          Some phm

      match loop phm 0 with
      | Some phm  -> PersistentHashMap.isEmpty phm
      | None      -> false

    static member ``PHM should behave as Map`` (vs : Action []) =
      let compare map (phm : PersistentHashMap<_, _>) =
        let empty =
          match map |> Map.isEmpty, phm |> PersistentHashMap.isEmpty with
          | true  , true
          | false , false -> true
          | _     , _     -> false

        let visitor k v =
          match map |> Map.tryFind k with
          | Some fv -> v = fv
          | _       -> false

        PersistentHashMap.checkInvariant phm
        && (PersistentHashMap.length phm = map.Count)
        && empty
        && PersistentHashMap.visitKeyValues visitor phm

      let ra = ResizeArray<int> ()

      let rec loop map (phm : PersistentHashMap<_, _>) i =
        if i < vs.Length then
          match vs.[i] with
          | Add (k, v)  ->
            ra.Add k
            let map = map |> Map.add k v
            let phm = PersistentHashMap.set k v phm
            compare map phm && loop map phm (i + 1)
          | Remove r    ->
            if ra.Count > 0 then
              let r   = abs r % ra.Count
              let k   = ra.[r]
              ra.RemoveAt r
              let map = map |> Map.remove k
              let phm = PersistentHashMap.unset k phm
              compare map phm && loop map phm (i + 1)
            else
              loop map phm (i + 1)
        else
          true

      loop Map.empty PersistentHashMap.empty 0

  open FsCheck

  let run () =
#if DEBUG
    let testCount = 100
#else
    let testCount = 1000
#endif

    //Properties.``PHM toArray must contain all added values`` [|(1, "")|] |> printfn "%A"

    let config = { Config.Quick with MaxTest = testCount; MaxFail = testCount }
    Check.All<Properties> config
    ()

[<EntryPoint>]
let main argv =
  try
    PropertyTests.run ()
    0
  with
  | e ->
    printfn "Caught: %s" e.Message
    999
