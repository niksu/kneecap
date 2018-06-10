(*
   Copyright 2015 Nik Sultana

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module general

open System

/// Identity function.
let I x = x

/// Generate a list containing elements between "j" and "i" inclusive.
let enumerate_j j i =
  assert (j <= i)
  let rec enumerate' acc i =
    if i = j then j :: acc
    else enumerate' (i :: acc) (i - 1)
  in enumerate' [] i

(*Given an i, this function generates a list with i+1 items: [0; 1; ...; i-1; i]*)
let enumerate i = enumerate_j 0 i

(*generate a list containing elements starting at j and ending at (j + i) inclusive*)
let enumerate_from j i = enumerate_j j (j + i)

(*Generates list of BV sorts between 1 and max, inclusive,
  in that order.*)
let sort_range (ctxt : Microsoft.Z3.Context) max =
  List.fold (fun acc i ->
    if i > 0 then ctxt.MkBitVecSort(uint32 i) :: acc
    else acc (*since bv sorts must be >0*)) []
    (enumerate max)
  |> List.rev

let rec log2' (x : uint32) (acc : uint32) =
  (*FIXME this check can be lifed out of the recursive loop*)
  if x % uint32 2 = uint32 1 then
    log2' (x - uint32 1) (acc + uint32 1)
  else
    let acc' = uint32 1 + acc
    if x < uint32 2 then acc'
    else log2' (x / uint32 2) acc'
(*Ceiling log2 for uin32 values*)
let log2 (x : uint32) = log2' x (uint32 0)

let extract_raw_witness (model : Microsoft.Z3.Model) (name : Microsoft.Z3.BitVecExpr) =
  model.Eval(name, true)

(*If "pad" then we pad the returned value with 0s, to match the expected width of the solution.*)
let extract_concatted_witnesses (ctxt : Microsoft.Z3.Context) (pad : bool) (model : Microsoft.Z3.Model) (names : Microsoft.Z3.BitVecExpr list) =
  let raw_ws : (uint32 * Microsoft.Z3.BitVecExpr) list =
    List.map (fun (e : Microsoft.Z3.BitVecExpr) ->
      (e.SortSize, extract_raw_witness model e :?> Microsoft.Z3.BitVecExpr)) names
  let total_name_sort_size =
    List.fold (fun acc (name : Microsoft.Z3.BitVecExpr) -> acc + name.SortSize) 0u names
  let total_raw_widths = List.fold (fun acc (width, _) -> acc + width) 0u raw_ws

  let raw_w =
    match raw_ws with
    | [] -> failwith "'names' cannot be empty"
    | [(_, witness)] -> witness
    | (_, w) :: ws ->
      List.fold (fun acc (_, e) ->
        ctxt.MkConcat (acc, e))
       w ws
  assert (raw_w.SortSize = total_name_sort_size) (*name and its value must have same sort size*)
  assert (raw_w.SortSize % 8u = 0u) (*sort size must be divisible by 8*)
(*  let pre_array = ref (Numerics.BigInteger.Parse(raw_w.ToString()).ToByteArray())*)

  let numeric_w =
    match raw_ws with
    | [] -> failwith "'names' cannot be empty"
    | [(_, witness)] ->
      Numerics.BigInteger.Parse(witness.ToString())
    | (_, w) :: ws ->
      let w' = Numerics.BigInteger.Parse(w.ToString())
      List.fold (fun acc (width, e) ->
(*        ctxt.MkConcat (acc, e))*)
        let e' = Numerics.BigInteger.Parse(e.ToString())
        (acc <<< int width) ||| e')
       w' ws
  let pre_array = ref (numeric_w.ToByteArray())
  let expected_width = total_name_sort_size / uint32 8(*bitwidth of byte*)
  (*Check if we leading 00s have been inserted -- this happens when the value is close to the maximum number the width can represent.*)
  if uint32 pre_array.contents.Length = expected_width + 1u then
    if not config.solver_is_big_endian then System.Array.Reverse(!pre_array)
    Array.Resize(pre_array, int(*FIXME precision loss from uint32?*) expected_width)
    if not config.solver_is_big_endian then System.Array.Reverse(!pre_array)
  if pad then
    (*Pad up to the expected number of bytes. Extended an array to a bigger size will
      result in the new cells initialised to 0, which is what we want.*)
    if uint32 pre_array.contents.Length < expected_width then
      Array.Resize(pre_array, int(*FIXME precision loss from uint32?*) expected_width)
  assert (uint32 pre_array.contents.Length = expected_width)
  !pre_array


let to_byte_string (bs : byte []) : string =
  Array.fold (fun acc (b : byte) ->
                acc + sprintf "%s " (String.Format("{0:X2}", b))) "" bs

let rec list_insert' (n : int) (x : 'a) (acc : 'a list) (l : 'a list) : 'a list =
  if n = 0 then List.rev acc @ x :: l
  else
    match l with
    | [] -> failwith "Unexpected end of list"
    | y :: rest ->
      list_insert' (n - 1) x (y :: acc) rest
(*Inserts an element at the nth position in a list*)
let list_insert (n : int) (x : 'a) (l : 'a list) : 'a list =
  assert (n >= 0)
  assert (n <= List.length l)
  list_insert' n x [] l

(*Reverse the bit order in a byte*)
let reverse_bits (b : byte) : byte =
  let mutable b = b
  let mutable i = 8
  let mutable b' : byte = 0uy
  while (i > 0) do
    b' <- b' <<< 1
    b' <- b' ||| (b &&& 1uy)
    b <- b >>> 1
    i <- i - 1
  done
  b'

(*Reverse byte order and/or bit order within each byte*)
let process_bytes (do_reverse_bytes : bool) (do_reverse_bits : bool) (bs : byte[]) : byte[] =
  let byte_fun (b : byte) =
    if do_reverse_bits then reverse_bits b
    else b
  let byte_array (bs : byte[]) =
    if do_reverse_bytes then System.Array.Reverse bs
    bs
  Array.map byte_fun (byte_array bs)

let bytes_to_string (bytes : byte[]) : string =
  Array.fold (fun (acc : string) (x : byte) -> acc + sprintf "%s " (String.Format("{0:X2}", x))) "" bytes

let print_result (pckt_opt : byte[] option) : unit =
  let result =
    match pckt_opt with
    | None -> ""
    | Some bytes ->
      sprintf "%d bytes " (Array.length bytes) + bytes_to_string bytes
  printfn "result=%s" result


open Microsoft.Z3

let concat_bvs (ctxt : Context) (bvs : BitVecExpr list) : BitVecExpr =
  match bvs with
  | [] -> failwith "Cannot concat_bvs an empty list of bvs"
  | [bv] -> bv
  | _ ->
    List.fold (fun acc bv -> ctxt.MkConcat (acc, bv)) 
      (List.head bvs) (List.tail bvs)

(*Translate a byte into a bitvector (of size 8)*)
let byte_to_bv (ctxt : Context) (b : byte) : BitVecExpr =
  ctxt.MkBV (uint32 b, 8u) :> BitVecExpr

(*Create BVs from byte[], this is used for Foreign_Field*)
(*NOTE bytes are encoded in the order given, and not transformed in any way.*)
let bytes_to_bv (ctxt : Context) (bs : byte[]) : BitVecExpr =
  assert (Array.length bs > 0)
  if Array.length bs = 1 then byte_to_bv ctxt bs.[0]
  else
    Array.fold
      (fun acc b -> ctxt.MkConcat (acc, byte_to_bv ctxt b))
      (byte_to_bv ctxt bs.[0]) bs.[1..]

let byte_to_boollist (b : byte) : bool list =
  let bits_in_a_byte = 8
  enumerate (bits_in_a_byte - 1)
  |> List.fold (fun acc position ->
      let bit_is_set = 1uy <<< position
      (b &&& (1uy <<< position) = bit_is_set) :: acc) []

let bytes_to_boollist (bs : byte[]) : bool list =
  Array.map byte_to_boollist bs
  |> List.concat
