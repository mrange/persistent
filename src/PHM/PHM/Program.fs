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
module PersistentHashMap =
  open System

  type PHM<'K, 'V when 'K :> IEquatable<'K>>  =
    | Empty
    | KeyValue        of int*'K*'V
    | Bitmap          of int*PHM<'K, 'V> []
    | HashCollision   of int*(int*'K*'V) []

  module Details =
    [<Literal>]
    let TrieShift     = 4
    [<Literal>]
    let TrieMaxShift  = 32
    [<Literal>]
    let TrieMaxNodes  = 16  // 1 <<< downshift
    [<Literal>]
    let TrieMask      = 15u // maxNodes - 1

    let inline localHash  h s = (h >>> s) &&& TrieMask;
    let inline bit        h s = 1u <<< int (localHash h s)
    let inline popcount i =
      // From: http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel
      //  x86/x64 support popcnt but that isn't available in ILAsm
      let mutable v = i
      v <- v - ((v >>> 1) &&& 0x55555555)
      v <- (v &&& 0x33333333) + ((v >>> 2) &&& 0x33333333)
      ((v + (v >>> 4) &&& 0xF0F0F0F) * 0x1010101) >>> 24

    let inline copyArray (vs : _ []) =
      let nvs = Array.zeroCreate vs.Length
      let rec loop i =
        if i < vs.Length then
          nvs.[i] <- vs.[i]
          loop (i + 1)
      loop 0
      nvs

    let inline copyArrayMakeHoleLast (vs : _ []) =
      let nvs = Array.zeroCreate (vs.Length + 1)
      let rec loop i =
        if i < vs.Length then
          nvs.[i] <- vs.[i]
          loop (i + 1)
      loop 0
      nvs

    let inline  copyArrayMakeHole holebit bitmap (vs : _ []) =
      let holemask  = holebit - 1;
      let nvs       = Array.zeroCreate (vs.Length + 1)

      let rec first bitmap i =
        if (bitmap &&& holemask) <> 0 then
          nvs.[i] <- vs.[i]
          first (bitmap &&& (bitmap - 1)) (i + 1)
        else
          second i
      and second i =
        if i < vs.Length then
          nvs.[i] <- vs.[i]
          second (i + 1)

      nvs


    // TODO: boxing seems optimized away, verify
    let inline hashOf<'T when 'T :> IEquatable<'T>> (v : 'T)           = (box v).GetHashCode ()
    let inline equals<'T when 'T :> IEquatable<'T>> (l : 'T) (r : 'T)  = l.Equals r

  open Details

module Tests =
  type Properties () =
    static member ``popcount count number of set bits`` i =
      let expected  =
        let rec loop c v =
          if v <> 0 then
            loop (c + 1) (v &&& (v - 1))
          else
            c
        loop 0 i
      System.Diagnostics.Debugger.Break ()
      let actual    = PersistentHashMap.Details.popcount i
      expected      = actual

[<EntryPoint>]
let main argv =
  let config = { FsCheck.Config.Quick with MaxFail = 10000; MaxTest = 1000}
  FsCheck.Check.All<Tests.Properties> config
//  let e = PersistentHashMap.Empty
//  let ov = PersistentHashMap.tryFind 1 e
  0
