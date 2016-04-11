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

(*
Translation of Quotations.Expr into constraint expressions.
I call constraint expressions an "intermediate language", since the
target language is the backend solver's expression language.
*)

module ir_translation

open general
open expressions

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns

type operator =
  | Oite (*IfThenElse (..., ..., ...)*)
  | Onot (*Call (None, Not, [...])*)
  | Oplus (*op_Addition*)
  | Ominus (*op_Subtraction*)
  | Otimes (*op_Multiply*)
  | Odiv (*op_Division*)
  | Orshift (*op_RightShift*)
  | Olshift (*op_LeftShift*)
  | Oeq (*Call (None, op_Equality, [...])*)
  | Olt (*Call (None, op_LessThan, [...])*)
  | Olte (*Call (None, op_LessThanOrEqual, [...])*)
  | Ogt (*Call (None, op_GreaterThan, [...])*)
  | Ogte (*Call (None, op_GreaterThanOrEqual, [...])*)
  | CurrApply of string (*Call (None, (some non-theory function), [(singleton expression)])*)

let arity = function
  | Oite -> 3
  | Onot -> 1
  | Oplus -> 2
  | Ominus -> 2
  | Otimes -> 2
  | Odiv -> 2
  | Orshift -> 2
  | Olshift -> 2
  | Oeq -> 2
  | Olt -> 2
  | Olte -> 2
  | Ogt -> 2
  | Ogte -> 2
  | CurrApply _ -> 1 (*Application of curried functions*)

let operator_to_string = function
  | Oite -> "Oite"
  | Onot -> "Onot"
  | Oplus -> "Oplus"
  | Ominus -> "Ominus"
  | Otimes -> "Otimes"
  | Odiv -> "Odiv"
  | Orshift -> "Orshift"
  | Olshift -> "Olshift"
  | Oeq -> "Oeq"
  | Olt -> "Olt"
  | Olte -> "Olte"
  | Ogt -> "Ogt"
  | Ogte -> "Ogte"
  | CurrApply f_name -> "(CurrApply " + f_name + ")"

(*Representation of source and intermediate expressions, during different
  stages of translation.*)
type acc_data =
    (*An expr in the source language*)
  | Source_Expr of Expr
    (*An operator. When combiend with operands (in the IL) it
      will create new expressions in the IL*)
  | Operator of operator
    (*A fully-translated logical expression in the IL*)
  | Operand of expression<const_name, location>
    (*A fully-translated arithemtical expression in the IL*)
  | Operand_Arit of arithmetical_exp<const_name, location>

(*tuck moves i, past any number of Source_Exprs, up to an Operator,
  then hands over to continue_tuck.*)
let rec tuck (i : acc_data) (acc : acc_data list) (l : acc_data list) : acc_data list =
  match l with
  | (Operator op as o) :: rest ->
      List.rev (o :: acc) @ list_insert (arity op - 1 - List.length acc) i rest
  | (Source_Expr _ as s) :: rest ->
      tuck i (s :: acc) rest
  | _ ->
    failwith ("Tuck encountered an unexpected intermediate value: " +
        l.ToString() + " while inserting " + i.ToString() + ", acc=" + acc.ToString())

(*Starts with a singleton list containing a Source_Expr, and terminates
  when we have a singleton list containing an Operand.
  In the mean time, we'll have a list of intermediate conversions between
  the source and intermediate languages. If O is an operator, and S0 S1 S2 S3
  are source operands (i.e., Source_Exprs) then the acc transitions will look
  like the following:
  [S0; ...]
  [S1; S2; O; ...] expanding S0 into a binary operator O applied to S1 and S2
  or
  [S1; S2; S3; O; ...] if O is a ternary operator.
  Assuming O is binary, eventually we'll have the following configuration
  [I1; S2; O; ...] where I1 is an expression in the intermediate language.
  We then tuck I1 behind O, so we can focus on translated S2.
  [S2; O; I1; ...]
  Eventually ending up in this configuration
  [I2; O; I1; ...] (If O is ternary, then we'd do another tuck, and translate S3)
  And then, as before, tuck I2 behind O (and any other IR expressions)
  [O; I1; I2; ...]
  We then interpret O applied to I1 and I2 in the IR, to give us the
  the expression I in the IR:
  [I; ...]
*)
let rec fsexpr_to_cexp (acc : acc_data list) =
  match acc with
  | [Operand e] -> e
  | (Operand _ as i) :: rest ->
    tuck i [] rest
    |> fsexpr_to_cexp
  | (Operand_Arit _ as i) :: rest ->
    tuck i [] rest
    |> fsexpr_to_cexp
  | Operator o :: rest ->
    begin
    let acc' =
      match o with
      | Oite ->
        match rest with
        | Operand x1 :: Operand x2 :: Operand x3 :: acc' ->
            Operand (Ite (x1, x2, x3)) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Onot ->
        match rest with
        | Operand x1 :: acc' ->
            Operand (Not x1) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Oplus ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
             Operand_Arit  (Plus (x1, x2)) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Ominus ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
            Operand_Arit (Minus (x1, x2)) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Otimes ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
            Operand_Arit (Times (x1, x2)) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Odiv ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
            Operand_Arit (Div (x1, x2)) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Orshift ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
            Operand_Arit (ShRight (x1, x2)) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Olshift ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
            Operand_Arit (ShLeft (x1, x2)) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Oeq ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
            Operand (Atom (Eq (x1, x2))) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Olt ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
            Operand (Atom (Lt (x1, x2))) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Olte ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
            Operand (Atom (LtEq (x1, x2))) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Ogt ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
            Operand (Atom (Gt (x1, x2))) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | Ogte ->
        match rest with
        | Operand_Arit x1 :: Operand_Arit x2 :: acc' ->
            Operand (Atom (GtEq (x1, x2))) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
      | CurrApply f_name ->
        match rest with
        | Operand_Arit x1 :: acc' ->
            Operand_Arit (Apply (f_name, x1)) :: acc'
        | _ -> failwith ("While handling " + operator_to_string o +
                         " found incorrect number or kind of arguments: " + rest.ToString())
    fsexpr_to_cexp acc'
    end
  | Source_Expr e :: rest ->
      match e with
      | Patterns.PropertyGet (_, inf, _) ->
        (*Name of a field at this level*)
        Operand_Arit (Const { idx = None; name = Some inf.Name; foreign = false }) :: rest
        |> fsexpr_to_cexp
      | Patterns.Value (v, _) ->
        let operand =
          (*Check what kind of literal we have: bool, int, or string.*)
          match v with
          | :? bool as v -> Operand (ValB v)
          | :? int as v -> Operand_Arit (ValI v)
          | :? string as v -> Operand_Arit (ValS v)
          | _ -> failwith "Unsupported value type"(*FIXME give more info*)
        operand :: rest
        |> fsexpr_to_cexp
      | Patterns.NewUnionCase (_, [Patterns.Value (v, _); Patterns.NewUnionCase (_, [])]) ->
        let operand =
          match v with
          | :? string as v -> v
          | _ -> failwith "Unsupported value type"(*FIXME give more info*)
        Operand_Arit (Const { idx = None; name = Some operand; foreign = true }) :: rest
        |> fsexpr_to_cexp
      | Patterns.IfThenElse (x1, x2, x3) ->
        fsexpr_to_cexp ([Source_Expr x1; Source_Expr x2; Source_Expr x3] @ (Operator Oite) :: rest)
      | Call (_, operate, args) ->
        let (operator, operands) =
          match operate.Name with
          | "Not" ->
            match args with
            | [x1] -> (Operator Onot, [Source_Expr x1])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_Addition" ->
            match args with
            | [x1; x2] -> (Operator Oplus, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_Subtraction" ->
            match args with
            | [x1; x2] -> (Operator Ominus, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_Multiply" ->
            match args with
            | [x1; x2] -> (Operator Otimes, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_Division" ->
            match args with
            | [x1; x2] -> (Operator Odiv, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_RightShift" ->
            match args with
            | [x1; x2] -> (Operator Orshift, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_LeftShift" ->
            match args with
            | [x1; x2] -> (Operator Olshift, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_Equality" ->
            match args with
            | [x1; x2] -> (Operator Oeq, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_LessThan" ->
            match args with
            | [x1; x2] -> (Operator Olt, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_LessThanOrEqual" ->
            match args with
            | [x1; x2] -> (Operator Olte, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_GreaterThan" ->
            match args with
            | [x1; x2] -> (Operator Ogt, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | "op_GreaterThanOrEqual" ->
            match args with
            | [x1; x2] -> (Operator Ogte, [Source_Expr x1; Source_Expr x2])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
          | _ -> (*I assume the operator to be intended for interpretation by a layer*)
            match args with
            | [x1] -> (Operator (CurrApply operate.Name), [Source_Expr x1])
            | _ -> failwith "Operator given incorrect number of arguments"(*FIXME give more info*)
        fsexpr_to_cexp (operands @ operator :: rest)
      | _ -> failwith ("Unsupported reflected expression: " + e.ToString())
  | _ -> failwith "Cannot convert expression"(*FIXME give more info*)


(*Extract a name from an Expr -- we expect the Expr to consist solely of a name.
  If the Expr contains anything other than a name, then fail.*)
let name_from_expr (e : Expr) : string =
  match e with
  | Patterns.PropertyGet (_, inf, _) ->
      inf.Name
  | _ -> failwith "Expr wasn't a name"
