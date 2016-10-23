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
    | Array           of int*PHM<'K, 'V> []
    | HashCollision   of int*'K []*'V []

  module Details =

    [<Measure>]
    type Bitmap

    [<Measure>]
    type Hash

    [<Literal>]
    let downshift     = 4

    [<Literal>]
    let maxNodes      = 16 // 1 <<< downshift

    [<Literal>]
    let mask          = 15 // maxNodes - 1

    let inline popcount i =
      // From: http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel
      //  x86/x64 support popcnt but that isn't available in ILAsm
      let mutable v = i
      v <- v - ((v >>> 1) &&& 0x55555555)
      v <- (v &&& 0x33333333) + ((v >>> 2) &&& 0x33333333)
      ((v + (v >>> 4) &&& 0xF0F0F0F) * 0x1010101) >>> 24

    // TODO: boxing seems optimized away, verify
    let inline hashOf<'T when 'T :> IEquatable<'T>> (v : 'T)           = (box v).GetHashCode ()
    let inline equals<'T when 'T :> IEquatable<'T>> (l : 'T) (r : 'T)  = l.Equals r

    let inline index hash shift = (hash >>> shift) &&& mask

    let inline keyValue h k v =
      KeyValue (h, k ,v)

    let inline hashCollision2 h k1 v1 k2 v2 =
      HashCollision (h, [|k1; k2|], [|v1; v2|])

    let rec array2 s h1 k1 v1 h2 k2 v2 =
      System.Diagnostics.Debug.Assert (h1 <> h2)
      let ns    = Array.zeroCreate maxNodes
      let idx1  = index h1 s
      let idx2  = index h2 s
      if idx1 <> idx2 then
        ns.[idx1] <- keyValue h1 k1 v1
        ns.[idx2] <- keyValue h1 k1 v1
        let bmp = (1 <<< idx1) ||| (1 <<< idx2)
        Array (bmp, ns)
      else
        ns.[idx1] <- array2 (s >>> downshift) h1 k1 v1 h2 k2 v2
        let bmp = (1 <<< idx1)
        Array (bmp, ns)

  open Details

  let inline tryFind key map =
    let hash = hashOf key
    let rec loop hash shift key map =
      match map with
      | Empty               -> None
      | KeyValue (h, k, v)  ->
        if h = hash && equals k key then
          Some v
        else
          None
      | Array (bmp, ms)->
        let idx = index hash shift
        let bit = 1 <<< idx
        if (bit &&& bmp) <> 0 then
          loop hash (shift + downshift) key ms.[idx]
        else
          None
      | HashCollision (h, ks, vs) ->
        if h = hash then
          let rec iloop key ks vs i =
            if i < Array.length ks then
              let k = ks.[i]
              if equals k key then
                let v = Array.get vs i
                Some v
              else
                iloop key ks vs (i + 1)
            else
              None
          iloop key ks vs 0
        else
          None
    loop hash 0 key map

(*
  let inline add key value map =
    let hash = hashOf key
    let rec loop hash shift key value map =
      match map with
      | Empty               -> KeyValue (hash, k, v)
      | KeyValue (h, k, v)  ->
        if h == hash then
          hashCollision2 h k v key value
        else
          array2 shift h k v hash key value
      | Array (bmp, ms) ->
        let idx = index hash shift
        let bit = 1 <<< idx
        if (bmp &&& bit) = 0 then

          Array (bmp ||| bit)
        else
*)

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
