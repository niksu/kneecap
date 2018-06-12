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

module interpretation

open Microsoft.Z3
open general

(* I use "interpretations" to interpret string-encoded values (of arbitrary type)
in some meaningful way; and encode that into a bitvector.
Following this definition i originally typed interpretations as : string -> BitVecExpr.

An interpretation need not interpret a single value; it can be generalised to handle wildcards, such as in
  192.168.2.*
  192.168.*.4
  192.*.[1-27].[5,8]

I revised the type of interpretations to Context -> string -> BitVecExpr * BoolExpr
Instead of only producing a BV, it also produces a constraint over that BV.
That constraint describes the allowable range of values covered by the wildcard.

For example, I translate "192.168.2.*" as b1.b2.b3.b4 -- where "." here means concat,
and each "bi" is an 8 bit BV. Unlike the others, "b4" is not a literal; it
is a fresh constant -- this corresponds to the wildcarded value.
Now since the wildcard is "*", we don't constrain that constant -- it's
associated constraint is "true".

Now take 192.*.[1-27].[5,8]. It becomes b1.b2.b3.b4, where only "b1" is a
literal; all the others are fresh constant. "b2" is unconstrained, as we
saw before. "b3" and "b4" are constrained in the obvious way; we could simply
do this as a disjunction of values -- for example "(b4 = 5) || (b4 = 8)".
Perhaps we could use bitmasks to be more efficient.

We form the resulting BV by concatting all the "bi", and by conjoining all
of their propositions.
Since the introduced constant are fresh, there's no danger of interference
with other solutions -- at worst they'll contain garbage.

The interpretation of wildcards is protocol specific -- i.e., the actual
range of values may be sensitive to the protocol.
But the "meaning" of wildcards is intended to be standard -- i.e.,
"*", "[x,y]", "[x-y]" have the same meanings for all protocols.
*)
type interpretation = Context -> string -> BitVecExpr * BoolExpr

(*Given an array of strings (each of which is intended to encode an octet of bits
  in some way), and a function mapping an octet into a BV and a proposition
  (over that BV), then concat together all the resulting BVs, and conjoin together
  all the resulting propositions.
  This function is used to process MAC and IP addresses, allowing
  wildcards to be used in octets.*)
let interpretation_skeleton (ctxt : Context) (octets : string []) (f : string -> BitVecExpr * BoolExpr option) : BitVecExpr * BoolExpr =
  let result =
    Array.fold
     (fun (bv_acc, prop_acc) (bv, prop) ->
       let bv_acc' =
         match bv_acc with
         | None -> Some bv
         | Some bv_acc -> Some (ctxt.MkConcat (bv_acc, bv))
       let prop_acc' =
         match prop_acc, prop with
         | _, None -> prop_acc
         | None, Some fmla -> Some fmla
         | Some prop, Some fmla -> Some (ctxt.MkAnd (prop, fmla))
       (bv_acc', prop_acc')
       )
     (None, None) (Array.map f octets)
  match result with
  | None, _ -> failwith "Bitvector should have been generated"
  | Some bv, None -> (bv, ctxt.MkTrue())
  | Some bv, Some prop -> (bv, prop)

/// <summary>Interpret a string-encoded class of octets as a bitstring together with a constraint
/// over it. Without the constraint, we would only be able to interpret literal bitstrings.</summary>
/// <param name="interpret_wildcards">Indication whether function should interpret wildcards
/// --- if false, then only literals will be interpreted.</param>
/// <param name="decode_octet">Function that maps a string into a byte. For instance, for MAC
/// addresses it maps a hex numeral, but for IPv4 addresses it maps integers.</param>
let interpret_octet (interpret_wildcards : bool) (ctxt : Context) (decode_octet : string -> byte)
 (byt : string) : BitVecExpr * BoolExpr option =
  if byt = "*" then
    if not interpret_wildcards then
      failwith "interpret_octet was not expecting to find wildcard"
    (ctxt.MkBVConst("wild" + config.get_fresh (), 8u), None)
  else
    if byt.StartsWith "[" then
      if not interpret_wildcards then
        failwith "interpret_octet was not expecting to find wildcard"
      let byt = byt.Substring(1, byt.Length - 2)
      let c = ctxt.MkBVConst("range" + config.get_fresh (), 8u)
      let comma_sepped = byt.Split [|','|]
      let acceptable_values =
        Array.fold
          (fun acc (range : string) ->
            let hyphen_sepped : string[] = range.Split [|'-'|]
            assert (Array.length hyphen_sepped < 3) (*we cannot have expressions like "1-4-6"; they don't make sense*)
            let range : uint32 list =
              if Array.length hyphen_sepped = 1 then
                [System.Convert.ToUInt32(hyphen_sepped.[0])]
              else
                let min = System.Convert.ToInt32(hyphen_sepped.[0])
                let max = System.Convert.ToInt32(hyphen_sepped.[1])
                List.map (fun x -> uint32 x) (enumerate_j min max)
            range @ acc) [] comma_sepped : uint32 list
      let disjs =
        List.map (fun (x : uint32) -> ctxt.MkBV (x, 8u)) acceptable_values
        |> List.map (fun x -> ctxt.MkEq(c, x))
      (c, Some (ctxt.MkOr (Array.ofList disjs)))
    else
      (*the string must be a numeral otherwise*)
      (ctxt.MkBV(int (decode_octet byt), 8u) :> BitVecExpr, None)
