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

(*Analyse and process IR, to make bitwidths explicit*)

module ir_processing

open general
open expressions
open interpretation

open Microsoft.Z3

type constant_type =
  | Field of
      BitVecExpr * (*The constant used in the target language; i expect that this constant has already been determined.*)
      (byte[] -> byte[]) (*The transformer that processes a solver's solution (represented as an array of bytes,
                           in the solver's order, into an array of bytes that could be sent over the wire
                           -- for instance, by changing the bit and/or byte order of the array elements.*)
      (*FIXME i expect that i'll need an inverse transformer to process bytes from a PCAP
              file into a bitstring of the right order for the backend solver*)
  | Foreign_Field (*That is forever England*) of byte[] (*get a (suitably padded) array of bytes from other scopes. We will then build BV in the current context using this value.*)
    (*e.g., specifying an IP address, MAC address etc.
      For convenience, each of these are presented as strings,
      but then need to be converted to their fixed-width
      representation (and in the right byte order).*)
    (*the parameter provides the means of translating strings into suitable (and correctly-sized bitvectors)*)
  | Interpretation of interpretation
    (*NOTE the literal must be of the right width!*)
  | Literal of BitVecExpr

type distinguished_constant_name = string

(*Dictionary of parameters to the "standard" bitvector theory.
  Includes constants used at this level, as well as names bound at higher protocols (and their values).
  This is used when translating constraint expressions into SMT-expressed constraints at this level.
*)
type distinguish_constant =
  { name : distinguished_constant_name; (*name that appears in the source and intermediate constraint*)
    width : uint32; (*how many bits are allocated to represent this value on the wire*)
    typ : constant_type; (*what this constant represents*)
  }

let lookup_dc (name : string) (dict : distinguish_constant list) : distinguish_constant =
  match List.filter (fun (d : distinguish_constant) -> d.name = name) dict with
  | [] -> failwith ("lookup_dc failed to find entry for " + name)
  | [r] -> r (*pass record along*)
  | _ -> failwith ("lookup_dc found multiple entrys for " + name)

(*FIXME might need to implement this more efficiently to handle large inputs*)
(*Add markers at the tips of the expression tree, to indicate what size
  bitvectors their representations should have.*)
let rec update_arith_widths (width : uint32) (dict : distinguish_constant list) (e : arithmetical_exp<const_name, location>) : arithmetical_exp<const_name, location> =
  match e with
  | Const c ->
    match c.name with
    | Some s ->
      let r = lookup_dc s dict
      let width_diff = width - r.width
      assert (width_diff >= 0u)
      ExtendWidth (width_diff, e)
    | _ -> failwith "Expected name for constant"
  | Apply (s, arg) ->
    let r = lookup_dc s dict
    assert (match r.typ with Interpretation _ -> true | _ -> false)
    let width_diff = width - r.width
    assert (width_diff >= 0u)
    ExtendWidth (width_diff, e)
  | ValI i ->
    let l = log2 (uint32 i)
    let width_diff = width - l
    assert (width_diff >= 0u)
    SetWidth (width, e)
  | Plus (e1, e2) ->
    Plus (update_arith_widths width dict e1, update_arith_widths width dict e2)
  | Minus (e1, e2) ->
    Minus (update_arith_widths width dict e1, update_arith_widths width dict e2)
  | Times (e1, e2) ->
    Times (update_arith_widths width dict e1, update_arith_widths width dict e2)
  | Div (e1, e2) ->
    Div (update_arith_widths width dict e1, update_arith_widths width dict e2)
  | ShLeft (e1, e2) ->
    ShLeft (update_arith_widths width dict e1, update_arith_widths width dict e2)
  | ShRight (e1, e2) ->
    ShRight (update_arith_widths width dict e1, update_arith_widths width dict e2)
  | ValS _ ->
    failwith "Strings aren't currently supported as values; they may only be given to Interpretations."
  | _ -> failwith "This form of expression is not supported by update_arith_widths"(*FIXME give more info*)

(*FIXME might need to implement this more efficiently to handle large inputs*)
(*Work out how many bits are required to represent the terms in an arithmetical expression,
  taking the maximum, in order to be able to produce well-formed bitvector expressions*)
let rec calc_arith_widths (dict : distinguish_constant list) (e : arithmetical_exp<const_name, location>) : uint32 =
  match e with
  | Const c ->
    match c.name with
    | Some s ->
      let r = lookup_dc s dict
      r.width
    | _ -> failwith "Expected name for constant"
  | Apply (s, arg) ->
    let r = lookup_dc s dict
    assert (match r.typ with Interpretation _ -> true | _ -> false)
    r.width
  | ValI i -> log2 (uint32 i)
  | Plus (e1, e2) ->
     max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
  | Minus (e1, e2) ->
     max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
  | Times (e1, e2) ->
     max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
  | Div (e1, e2) ->
     max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
  | ShLeft (e1, e2) ->
     max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
  | ShRight (e1, e2) ->
     max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
  | ValS _ ->
      failwith "Strings aren't currently supported as values; they may only be given to Interpretation."
  | _ -> failwith "This form of expression is not supported by update_arith_widths"(*FIXME give more info*)

(*FIXME might need to implement this more efficiently to handle large inputs*)
let rec annotate_bv_widths (dict : distinguish_constant list) (e : expression<const_name, location>) : expression<const_name, location> =
  match e with
  | Atom (Eq (e1, e2)) ->
      let w = max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
      let e1' = update_arith_widths w dict e1
      let e2' = update_arith_widths w dict e2
      Atom (Eq (e1', e2'))
  | Atom (Lt (e1, e2)) ->
      let w = max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
      let e1' = update_arith_widths w dict e1
      let e2' = update_arith_widths w dict e2
      Atom (Lt (e1', e2'))
  | Atom (Gt (e1, e2)) ->
      let w = max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
      let e1' = update_arith_widths w dict e1
      let e2' = update_arith_widths w dict e2
      Atom (Gt (e1', e2'))
  | Atom (LtEq (e1, e2)) ->
      let w = max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
      let e1' = update_arith_widths w dict e1
      let e2' = update_arith_widths w dict e2
      Atom (LtEq (e1', e2'))
  | Atom (GtEq (e1, e2)) ->
      let w = max (calc_arith_widths dict e1) (calc_arith_widths dict e2)
      let e1' = update_arith_widths w dict e1
      let e2' = update_arith_widths w dict e2
      Atom (GtEq (e1', e2'))
  | ValB _ -> e
  | Not e' -> Not (annotate_bv_widths dict e')
  | Ite (e1, e2, e3) ->
      let e1' = annotate_bv_widths dict e1
      let e2' = annotate_bv_widths dict e2
      let e3' = annotate_bv_widths dict e3
      Ite (e1', e2', e3')
