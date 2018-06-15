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

module packets

open Microsoft.Z3
open general
open expressions
open ir_translation
open interpretation
open ir_processing
open z3_translation

(*
FIXME what might need fixing:
1. byte ordering
2. bit ordering within bytes
3. committing to uint32 everywhere, rather than mixing

probably will handle 1&2 outside the solver, otherwise need to have previously translated the constraints over to work wrt the required orderings.
*)

[<AbstractClass>]
type packet () =
  (*In general a solver will need to be invoked to come up with, or check,
    a packet's field values. This is where we initialise the solver's context.*)
  let ctxt = new Context()
  let slv = ctxt.MkSolver()
  let mutable model = None

  member this.Dispose () : unit =
    match model with
    | None -> ()
    | Some (mdl : Model) -> mdl.Dispose ()
    slv.Dispose ()
    ctxt.Dispose ()
  interface System.IDisposable with
    member this.Dispose () : unit = this.Dispose ()

  (*Returns width of a packet in bits*)
  (*FIXME actually returns _maximum_ width of a packet in bits?*)
  abstract member packet_size : uint32

  (*The constant that is interpreted to be a packet at this layer*)
  abstract member packet_bv : BitVecExpr

  (*Specifies a protocol-specific task to be carried out before
    the solver is invoked. For instance, this could involve
    recursively calling "generate" of encapsulated packets -- they will raise
    an exception if an impossibility is encountered at those levels,
    otherwise they'll yield a candidate for "payload" value.*)
  abstract member pre_generate : unit -> bool

  (*Our constraints have already been collected and sent to the solver eagerly.
    We now invoke the solver, cache the model (if there is one) and report back
    whether a model could be obtained.*)
  member this.generate () : bool =
    (*Run protocol-specific preprocessing step before generating a result;
      this step could involve recursively obtaining payload values from
      encapsulated packets.*)
    if not (this.pre_generate ()) then
      // pre_generate() failed -- consequently generate() has been aborted
      false
    else
      let (mdl_opt, result) =
        match slv.Check () with
        | Status.SATISFIABLE -> Some slv.Model, true
        | Status.UNSATISFIABLE -> None, false
        | _ -> failwith "Received unknown result from the solver"
      model <- mdl_opt
      result

  member this.context = ctxt
  member this.solver = slv
  member this.solution
    with get () = model
    and set (value) = model <- value

  (*Try to add a constraint to the solver so that the next (and subsequent)
    invocation of "generate" will return a different packet from the current solution.
    Return true iff this could be done.*)
  member this.constrain_different_flat () : bool =
    match model with
    | None -> false
    | Some mdl ->
      let w = extract_raw_witness mdl this.packet_bv (*FIXME does extract_raw_witness also include a potential payload? If yes then we're overlapping with "override this.constrain_different" below*)
      slv.Assert (ctxt.MkNot (ctxt.MkEq (this.packet_bv, w)))
      true
  abstract constrain_different : unit -> bool
  default this.constrain_different () = this.constrain_different_flat ()

  (*Protocol specific fields, constants, and interpretation*)
  abstract distinguished_constants : distinguish_constant list

  abstract member extract_field_value : string -> byte[] option
  (*Extract the witness for a constant as a byte array.
    Returns None if a model hasn't been generated yet.*)
  default this.extract_field_value (field_name : string) : byte[] option =
    match model with
    | None -> None
    | Some mdl ->
      let r = lookup_dc field_name this.distinguished_constants
      match r.typ with
      | Field (bv_const, byte_proc) ->
         extract_concatted_witnesses ctxt true mdl [bv_const]
         (*The byte_proc function should see to the byte ordering,
           bit ordering fine, and any padding requirements.*)
         |> byte_proc
         |> Some
      | _ -> failwith ("This doesn't resolve to a field: " + field_name)

  (*Generalises extract_field_value, but
    involves applying a single byte_proc to all concatted fields' bytes*)
  abstract member extract_concatted_field_values : (byte[] -> byte[]) -> string list -> byte[] option
  (*Extract the witness for a list of constants as a byte array.
    Returns None if a model hasn't been generated yet.*)
  default this.extract_concatted_field_values (byte_proc : byte[] -> byte[]) (field_names : string list) : byte[] option =
    match model with
    | None -> None
    | Some mdl ->
        List.map (fun field_name ->
          let r = lookup_dc field_name this.distinguished_constants
          match r.typ with
          | Field (bv_const, _(*ignore field-specific byte_proc -- we apply a single one across all concatted bytes*)) ->
            bv_const
          | _ -> failwith ("This doesn't resolve to a field: " + field_name)) field_names
        |> extract_concatted_witnesses ctxt true mdl
          (*The byte_proc function should see to the byte ordering,
            bit ordering fine, and any padding requirements.*)
        |> byte_proc
        |> Some

  (*Extract the solution we obtained for a packet: produce the PDU for
    this protocol, as it is to go on the wire. This means that
    any byte and bit reordering needs to have been already carried out.
    This member is abstract since we don't know exactly which fields
    to pick out, how to interpret and compose them, etc -- we'll leave
    this to be specified at the protocol-specific level.*)
  abstract member extract_packet : unit -> byte[] option

  (*Mainly for debugging*)
  member this.assertion () : BoolExpr [] =
    slv.Assertions
  (*Push/pop constraints to solver, to enable finer and more flexible
    external manipulation of its state.*)
  member this.push_constraints () : unit =
    slv.Push ()
  member this.pop_constraints (?n : uint32) : unit =
    let n = defaultArg n 1u
    slv.Pop (n)


type encapsulation_handling_record =
  { packet_type : System.Type;
    (*NOTE handler is not purely-functional -- it may modify the payload_carrier*)
    handler : payload_carrier -> packet -> bool
  }

(*NOTE instead of having static list of supported protocols for encapsulation/encapsulating,
  i used a system of extensible hooks as a way of extending available supported protocols.
*)
and [<AbstractClass>] payload_carrier () =
  inherit packet ()
  let mutable carrying : packet option = None
  let mutable can_encapsulate : encapsulation_handling_record list = []
  let mutable can_be_encapsulated_in : encapsulation_handling_record list = []

  interface System.IDisposable with
    member this.Dispose () : unit = base.Dispose ()

  member this.encapsulated_packet = carrying

(*FIXME i don't think this is needed -- the rollback could be nontrivial
        to remove an encapsulated packet, since we might need to cancel some
        assertions made
  (*At the very least, we set carrying to None to remove an encapsulated packet,
    but we might also need to do some protocol-specific modifications,
    to change some fields.
    For instance, if we unencapsulate TCP from IP, we'd change IP's
    "protocol" field to be unconstrained.*)
  abstract member remove_encapsulated_packet : unit -> unit
*)

  (*Set up an encapsulation relationship between an instance of this class
    and an instance of packet. We do this by checking if a handler has
    been provided, and if so, then apply it to the packet instance.*)
  member this.encapsulate (encapped : packet) : payload_carrier =
(*
    let handlers =
      List.filter (fun ehr -> ehr.packet_type = encapped.GetType()) can_encapsulate
      |> List.map (fun x -> x.handler)
    match handlers with
    | [] -> failwith "Invalid encapsulation -- no handler available" (*FIXME give more info in the error message, mentioning the specific packet types.*)
    | [handler] ->
        if handler this encapped then
          carrying <- Some encapped
        else failwith "Packet failed encapsulation test" (*FIXME give more info in the error message*)
    | _ -> failwith "Packet encapsulation failed -- more than one handler present" (*FIXME give more info in the error message*)
*)
    (*FIXME check that encapped != this, otherwise packet will encapsulate itself*)
          carrying <- Some encapped
          this

  (*Causes constraint_different to ripple up the encapsulation chain*)
  override this.constrain_different () : bool =
    match this.solution with
    | None -> false
    | Some mdl ->
      let constrain_different_payload =
        match carrying with
        | None -> true
        | Some pckt -> pckt.constrain_different ()
      this.constrain_different_flat () && constrain_different_payload


(*Independent of all packets, we have theory-interpreted symbols (=, <, 4, etc).
  We now gain packet-interpreted symbols (related to constants that signify fields)
  and use them together with interpreted symbols to build expressions.
  We can also have special symbols that are imported from northside (i.e., from encapsulated packets).
  Their solutions are exported down to lower-layers (the encapsulating packets).

  FIXME current constraint: symbols may only move southwards, since we solve starting with the topmost layer.
        this is not a general constraint however. we could make partial solutions and refine them..
        this would enable more flexible inter-layer constraints... future work.  
*)
[<AbstractClass>]
type constrainable_payload_carrier () =
  inherit payload_carrier ()
  let mutable _constraint(*F\# does not approve if we call something "constraintt"*)
    = true (*initially we have the weakest possible constraint --
             this means that unless we constrain further, then any
             field values are acceptable.*)
  (*The names bound at this level; these are made available to lower levels.*)
  let mutable names : (string * distinguished_constant_name) list = []

  interface System.IDisposable with
    member this.Dispose () : unit = base.Dispose ()

  (*Reset constraints*)
  member this.unconstrain () = _constraint <- true

  (*Bind a name -- this will associating a name (presented as a string) with
    a protocol field. The scope of the name extends across all protocols in lower
    levels.*)
  member this.name (name : string, expr : Quotations.Expr) =
    if List.exists (fun (x, _) -> x = name) names then
      failwith "Name has already been bound at this scope" (*FIXME give Position-style info*) (*NOTE names bound in a sister scope aren't (can't be?) checked here*)
    else
      let field_name = name_from_expr expr
      (*Check if field_name does indeed resolve to a field name -- an
        exception is thrown by name_to_field otherwise*)
      ignore(this.name_to_field field_name)
      names <- (name, field_name) :: names

  (*Forget a name*)
  member this.unname (name : string) =
    List.partition (fun (x, _) -> x = name) names
    |> snd

  (*Forget all names*)
  member this.unname_all () = names <- []

  (* Get names (and solutions) from upper scopes via function call
     to the contained packet (which in turn recurses up whatever it
     encapsulates).
     NOTE the solutions need to be provided in a context-neutral form,
          since otherwise the receiving context might reject those value
          when asserted in formulas in the receiving context.*)
  member this.obtain_names (including_local : bool) : (string * byte[]) list =
    let upper_layer_names =
      match this.encapsulated_packet with
      | None -> []
      | Some pckt ->
          match pckt with
               (*FIXME must all packets in the stack really be of this type?*)
          | :? constrainable_payload_carrier ->
              (pckt :?> constrainable_payload_carrier).obtain_names true
          | _ -> failwith "Expected constrainable payload carrier"
    let my_names =
      List.map
        (fun (name, local_field_name) ->
           match this.extract_field_value local_field_name with
           | None -> failwith ("Unable to extract value of " + name)
           | Some bytes -> (name, bytes)) names
    (*Check for name clashes, and raise an exception.
      NOTE there cannot be a clash between protocol field names (which are fixed
           and programmer-defined) and "parameter" names that the user
           invents, since the two kinds of names are expressed differently
           -- we could say that they occupy different namespaces.*)
    (*FIXME naive*)
    List.iter
      (fun (foreign_name, _) ->
         List.iter
           (fun (local_name, _) ->
              if local_name = foreign_name then
                failwith ("Name clash: local=" + local_name + ", foreign=" + foreign_name))
           my_names)
      upper_layer_names
    upper_layer_names @
      (if not including_local then [] else my_names)


  (*Appending distinguish_constants with all the names (but not distinguish_constants)
    from this and higher layers*)
  member this.distinguish_constants_closure : distinguish_constant list =
    let dc_names =
      List.map
        (fun (n, bytes) -> {name = n; width = uint32 (Array.length bytes * 8); typ = Foreign_Field bytes})
        (this.obtain_names false)
    dc_names @ this.distinguished_constants

  (*Associate local and free (upper-layer) names with BV expressions to be used the constraint proposition.
    Determine widths of bitvectors (extending as needed).
    Translate into a BoolExpr for the solver.*)
  member this.constrain (expr : Quotations.Expr) =
    let translated_constraint, aux_constraint =
      fsexpr_to_cexp [Source_Expr expr]
      |> annotate_bv_widths this.distinguish_constants_closure
      |> cexp_to_BoolExpr this.context this.distinguish_constants_closure    
    this.solver.Assert (this.context.MkAnd (translated_constraint, aux_constraint))
    this

  (*Map the name of a field to the BV that is created for it.*)
  member this.name_to_field (s : string) : BitVecExpr =
    let r = lookup_dc s (*this.distinguished_constants*) this.distinguish_constants_closure
    match r.typ with
    | Field (bv, _) -> bv
    | _ -> failwith ("Expected " + s + " to resolve to a field, but it doesn't")

  (*Like constrain_different but can constrain to specific fields.*)
  member this.constrain_different_flex (expr : Quotations.Expr) : bool = (* FIXME sucky name; code needs cleaning*)
      match base.solution with
      | None -> false
      | Some mdl ->
        let field_str = name_from_expr expr (*FIXME i implicitly assume that expr contains a single field name*)
        let field_bv = this.name_to_field field_str
        let w = extract_raw_witness mdl field_bv
        this.solver.Assert (this.context.MkNot (this.context.MkEq (field_bv, w)))
        true

(*FIXME every time we iterate, and get a new model, will we need to garbage collect names from the context? can we use Push and Pop to help Z3 with this (i think it uses reference counting)*)

(*
(*Packet-level constants, such as field names (e.g., ethertype) or the names of
  their distinguished values (e.g., ethertype_ipv4) are given this type.
  It's deliberately constructed to provide a more programmer-friendly
  interface to the programmer, allowing them to specify constraints without
  much faff.*)
type packet_constant =
  interface System.IComparable with
    member this.CompareTo _ = failwith "This value should not be evaluated by F#"
*)

type address_carrier =
  interface
    /// Number of bytes needed to represent an address.
    abstract member address_width : uint8
    /// Function interpreting a string-encoding of an address.
    abstract member address_interpretation : interpretation
  end

let (<==) (p1 : payload_carrier) (p2 : payload_carrier) : payload_carrier = p1.encapsulate p2

let (+==) (p1 : payload_carrier) (p2s : payload_carrier list) =
  List.fold (fun (acc : payload_carrier) (p : payload_carrier) ->
    ignore(acc <== p)
    p) p1 p2s
    |> ignore
  ()
