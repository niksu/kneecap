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

module expressions

open general

type arithmetical_exp<'cst, 'lcn> =
  | Const of 'cst
  | Loc of 'lcn(*FIXME doesn't seem to be needed*)
  | ValI of int
  | ValS of string
  | Plus of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>
  | Minus of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>
  | Times of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>
  | Div of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>
  | ShLeft of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>
  | ShRight of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>
  | Apply of string * arithmetical_exp<'cst, 'lcn>
  (*ExtendWidth and SetWidth won't show up in the expressions we translate
    from F#'s Expr. It may be inserted only after analysing the expression
    tree to work out the required bitwidth for each argument to a logical
    atomic operator.*)
  (*ExtendWidth is used to extend the width of constants*)
  | ExtendWidth of uint32 * arithmetical_exp<'cst, 'lcn>
  (*SetWidth is used to set the width of literals; naturally this
    width must be greater than the width needed to represent each
    literal precisely*)
  | SetWidth of uint32 * arithmetical_exp<'cst, 'lcn>

type logical_atom<'cst, 'lcn> =
  | Eq of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>
  | Lt of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>
  | Gt of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>
  | LtEq of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>
  | GtEq of arithmetical_exp<'cst, 'lcn> * arithmetical_exp<'cst, 'lcn>

type expression<'cst, 'lcn> =
  | Atom of logical_atom<'cst, 'lcn>
  | ValB of bool
  | Not of expression<'cst, 'lcn>
  | Ite of expression<'cst, 'lcn> * expression<'cst, 'lcn> * expression<'cst, 'lcn>
(* NOTE the remainder aren't needed, since F#'s quotations system only returns ITEs it seems.
  | Or of expression<'cst, 'lcn> * expression<'cst, 'lcn>
  | And of expression<'cst, 'lcn> * expression<'cst, 'lcn>
  | Implies of expression<'cst, 'lcn> * expression<'cst, 'lcn>
*)

type location =
  { offset : uint32;
    width : uint32
  }

type const_name =
  { idx : uint32 option;
    name : string option;
    foreign : bool
  }
