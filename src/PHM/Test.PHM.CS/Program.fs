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
open FsCheck
open PHM.CS

open System
open System.Collections.Generic

[<AllowNullLiteral>]
type Empty () =
  inherit obj ()

type CopyArrayMakeHoleTestData = CopyArrayMakeHoleTestData of uint32*uint32*Empty []

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

  [<GeneralizableValue>]
  let empty = PersistentHashMap.Empty<_, _> ()

  let set k v (phm : IPersistentHashMap<_, _>) = phm.Set (k, v)

  let fromArray kvs =
    Array.fold
      (fun s (k, v) -> set k v s)
      empty
      kvs

  let toArray (phm : IPersistentHashMap<'K, 'V>) =
    phm
    |> Seq.map (fun kv -> kv.Key, kv.Value)
    |> Seq.toArray

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

  static member ``PHM must contain all values`` (vs : (int*string) []) =
    let expected  = vs |> Seq.groupBy fst |> Seq.map (fun (k, vs) -> k, (vs |> Seq.map snd |> Seq.last)) |> Seq.sortBy fst |> Seq.toArray
    let phm       = vs |> fromArray
    let actual    = phm |> toArray |> Array.sortBy fst

    let r = notIdentical expected actual
            && checkInvariant phm
            && expected = actual

    if r then
      r
    else
      printfn "%A" vs
      printfn "%s" ((vs |> fromArray).ToString ())
      false

[<EntryPoint>]
let main argv =
#if DEBUG
  let testCount = 100
#else
  let testCount = 1000
#endif

  Properties.``PHM must contain all values`` [|(2, ""); (1, ""); (0, "")|] |> ignore

  let config = { Config.Quick with MaxTest = testCount; MaxFail = testCount }
  Check.All<Properties>  config

  0
