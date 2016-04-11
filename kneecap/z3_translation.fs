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

(*Translate IR into Z3 expressions*)

module z3_translation

open general
open expressions
open ir_processing

open Microsoft.Z3

(*FIXME should semantics be overflow or not?*)
let rec aexp_to_BitVecExpr (ctxt : Context) (dict : distinguish_constant list) (e : arithmetical_exp<const_name, location>) : BitVecExpr * BoolExpr =
  match e with
  | ExtendWidth (w, Const c) ->
    let s =
      match c.name with
      | Some n ->
        assert (c.idx = None) (*Expecting this to be empty -- FIXME maybe i should just remove this field, it's not being used*)
        n
      | _ -> failwith "Expecting constant to have a name"
    let r = lookup_dc s dict
    let bv_c =
      match r.typ with
      | Field (bv, _) -> bv
      | Foreign_Field bytes ->
          assert c.foreign
          bytes_to_bv ctxt bytes
      | Interpretation _ -> failwith "Unexpected constant type"
      | Literal bv -> bv
    let bv_result =
      if w > 0u then
        ctxt.MkZeroExt (w, bv_c)
      else bv_c
    (bv_result, ctxt.MkTrue())
  | ExtendWidth (w, Apply (s, ValS arg)) -> (*FIXME maybe should pass Const to Apply, rather than a string? No real difference I think, except that c.foreign=false always, I'd expect*)
    let r = lookup_dc s dict
    let bv_c, prop =
      match r.typ with
      | Interpretation f -> f ctxt arg
      | _ -> failwith "Unexpected distinguished constant type"
    let bv_result =
      if w > 0u then
        ctxt.MkZeroExt (w, bv_c)
      else bv_c
    (bv_result, prop)
  | ExtendWidth (_, Apply (_, _)) -> failwith "This form of Apply is not supported"(*FIXME give more details*)
  | ExtendWidth _ -> failwith "ExtendWidth expression not supported"(*FIXME give more details*)

  | SetWidth (w, ValI i) ->
    (ctxt.MkBV (i, w) :> Microsoft.Z3.BitVecExpr, ctxt.MkTrue())
  | SetWidth _ -> failwith "SetWidth expression not supported"(*FIXME give more details*)

  | Const c -> failwith "Missing width annotation"(*FIXME give more details*)
  | Apply (s, arg) -> failwith "Missing width annotation"(*FIXME give more details*)
  | ValI i ->  failwith "Missing width annotation"(*FIXME give more details*)

  | Plus (e1, e2) ->
    let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
    let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
    (ctxt.MkBVAdd (e1', e2'), ctxt.MkAnd (prop1, prop2))
  | Minus (e1, e2) ->
    let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
    let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
    (ctxt.MkBVSub (e1', e2'), ctxt.MkAnd (prop1, prop2))
  | Times (e1, e2) ->
    let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
    let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
    (ctxt.MkBVMul (e1', e2'), ctxt.MkAnd (prop1, prop2))
  | Div (e1, e2) ->
    let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
    let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
    (ctxt.MkBVSDiv (e1', e2'), ctxt.MkAnd (prop1, prop2))
  | ShLeft (e1, e2) ->
    let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
    let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
    (ctxt.MkBVSHL (e1', e2'), ctxt.MkAnd (prop1, prop2))
  | ShRight (e1, e2) ->
    let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
    let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
    (ctxt.MkBVLSHR (e1', e2'), ctxt.MkAnd (prop1, prop2))
  | ValS _ ->
    failwith "Strings aren't currently supported as values; they may only be given to Interpretation."
  | _ -> failwith "This form of expression is not supported by aexp_to_Expr"(*FIXME give more info*)

(*Translate a constraint formula into a form that can be asserted to Z3*)
let rec cexp_to_BoolExpr (ctxt : Context) (dict : distinguish_constant list) (e : expression<const_name, location>) : BoolExpr * BoolExpr =
  match e with
  | ValB true -> (ctxt.MkTrue(), ctxt.MkTrue())
  | ValB false -> (ctxt.MkFalse(), ctxt.MkTrue())
  | Not e1 ->
    let e1', prop1 = cexp_to_BoolExpr ctxt dict e1
    (ctxt.MkNot e1', prop1)
  | Ite (e1, e2, e3) ->
      let e1', prop1 = cexp_to_BoolExpr ctxt dict e1
      let e2', prop2 = cexp_to_BoolExpr ctxt dict e2
      let e3', prop3 = cexp_to_BoolExpr ctxt dict e3
      ((ctxt.MkAnd (ctxt.MkImplies (e1', e2'), ctxt.MkImplies (ctxt.MkNot e1', e3'))),
       ctxt.MkAnd [|prop1; prop2; prop3|])
  | Atom (Eq (e1, e2)) ->
      let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
      let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
      (ctxt.MkEq (e1', e2'), ctxt.MkAnd (prop1, prop2))
  | Atom (Lt (e1, e2)) ->
      let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
      let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
      (ctxt.MkBVULT (e1', e2'), ctxt.MkAnd (prop1, prop2))
  | Atom (Gt (e1, e2)) ->
      let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
      let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
      (ctxt.MkBVUGT (e1', e2'), ctxt.MkAnd (prop1, prop2))
  | Atom (LtEq (e1, e2)) ->
      let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
      let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
      (ctxt.MkBVULE (e1', e2'), ctxt.MkAnd (prop1, prop2))
  | Atom (GtEq (e1, e2)) ->
      let e1', prop1 = aexp_to_BitVecExpr ctxt dict e1
      let e2', prop2 = aexp_to_BitVecExpr ctxt dict e2
      (ctxt.MkBVUGE (e1', e2'), ctxt.MkAnd (prop1, prop2))
