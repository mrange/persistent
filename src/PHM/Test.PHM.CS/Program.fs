open FsCheck
open PHM.CS

[<AllowNullLiteral>]
type Empty () =
  let x = 3

type CopyArrayMakeHoleData = CopyArrayMakeHoleData of int*uint32*Empty []

module Common =
  let notIdentical<'T when 'T : not struct> (f : 'T) (s : 'T) = obj.ReferenceEquals (f, s) |> not

  let popCount v =
    let rec loop c v =
      if v <> 0u then
        loop (c + 1u) (v &&& (v - 1u))
      else
        c
    loop 0u v

open Common

type Generators =
  static member CopyArrayMakeHoleData() =
    let g =
      gen {
        let! bitmap = Arb.generate<uint32>
        let length  = popCount bitmap |> int
        let! vs     = Gen.arrayOfLength length Arb.generate<Empty>
        let! bitpos = Arb.generate<uint32>
        return CopyArrayMakeHoleData (0, bitmap, vs)
      }
    { new Arbitrary<CopyArrayMakeHoleData> () with
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

  static member ``CopyArrayMakeHole copies the array and leaves a hole`` (CopyArrayMakeHoleData (bit, bitmap, vs)) =
    let expected  = Array.append vs [| null |]
    let actual    = PersistentHashMap.CopyArrayMakeHoleLast vs

    notIdentical expected actual
    && expected = actual

[<EntryPoint>]
let main argv = 
  let testCount = 100
  let config = { Config.Quick with MaxTest = testCount; MaxFail = testCount }
  Check.All<Properties>  config
  0
