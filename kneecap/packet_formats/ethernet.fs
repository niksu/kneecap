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

module ethernet

open general
open packets
open Microsoft.Z3
open interpretation
open ir_processing

/// <summary>Functor to generate CRC spec.</summary>
/// <param name="ctxt">Prover context</param>
/// <param name="polynomial_powers">Orders of the powers of the CRC polynomial</param>
/// <param name="buf_width">Width (in bits) of the buffer whose CRC will be calculated</param>
/// <param name="crc_width">Width (in bits) of the CRC</param>
type crc (ctxt : Context,
          polynomial_powers : int list,
          buf_width : uint32,
          crc_width : uint32) =
  do
    (*Check to see if the given polynomial is sensible for the given crc_width*)
    List.iter (fun degree -> if uint32 degree > crc_width then failwith "Unsuitable CRC polynomial") polynomial_powers

  let buf_and_shreg_width = buf_width + crc_width
  let max_length_bitwidth = log2 buf_and_shreg_width

  let generate_crc32 (s1 : BitVecExpr) (s2 : BitVecExpr) : BoolExpr =
    let state_components (s : BitVecExpr) =
      let n = ctxt.MkExtract(s.SortSize - uint32 1, s.SortSize - max_length_bitwidth, s)
      let buf = ctxt.MkExtract(s.SortSize - max_length_bitwidth - uint32 1, s.SortSize - max_length_bitwidth - buf_and_shreg_width, s)
      let reg = ctxt.MkExtract(s.SortSize - max_length_bitwidth - buf_and_shreg_width - uint32 1, uint32 0, s)
      n, buf, reg
    let n, buf, reg = state_components s1
    let n', buf', reg' = state_components s2
    let zero = ctxt.MkBV (0, max_length_bitwidth)
    let one = ctxt.MkBV (1, max_length_bitwidth)
    let fixpoint =
      ctxt.MkAnd
        [|ctxt.MkEq (n, zero);
          ctxt.MkEq (n', n);
          ctxt.MkEq (buf, ctxt.MkBV (0, buf_and_shreg_width));
          ctxt.MkEq (buf', buf);
          ctxt.MkEq (reg', reg)|]

    let crc_reg (buf : BitVecExpr) (reg : BitVecExpr) =
      let msb = ctxt.MkExtract(buf.SortSize - uint32 1, buf.SortSize - uint32 1, buf)
      enumerate (int crc_width - 1)
      |> List.map (fun i ->
          let xor_term e = ctxt.MkBVXOR (e, ctxt.MkExtract(crc_width - 1u, crc_width - 1u, reg))
          let e =
            if i = 0 then msb
            else ctxt.MkExtract(uint32 (i - 1), uint32 (i - 1), reg)
          if List.exists (fun x -> x = i) polynomial_powers then xor_term e else e)
    let step =
      ctxt.MkAnd
        [|ctxt.MkNot (ctxt.MkEq (n, zero));
          ctxt.MkEq (n', ctxt.MkBVSub (n, one));
          ctxt.MkEq (buf', ctxt.MkBVSHL (buf, ctxt.MkBV (1, buf.SortSize)));
          ctxt.MkEq (reg',
                      let l = crc_reg buf reg |> List.rev(*FIXME check*)
                      List.fold (fun x y -> ctxt.MkConcat (x, y)(*FIXME currying*)) (List.head l) (List.tail l)
                      (*ctxt.MkBVAdd (reg, ctxt.MkBV (1, uint32 trailer_sz))
                      ctxt.MkBVSub (reg, ctxt.MkBV (1, uint32 trailer_sz))*))|]
    ctxt.MkOr [|fixpoint; step|]

  let init_crc32_state (buf : BitVecExpr) : BitVecExpr =
    assert (buf.SortSize = buf_and_shreg_width)
    let n = ctxt.MkBV(buf.SortSize, max_length_bitwidth)
    let reg = ctxt.MkBV(0, uint32 crc_width)
    ctxt.MkConcat (n, ctxt.MkConcat (buf, reg))
 
  let rec unroll_crc32 (initial_state : BitVecExpr) (c : BitVecExpr) (acc : BoolExpr list) : Expr * BoolExpr =
    let c' = ctxt.MkFreshConst ("st_", initial_state.Sort) :?> BitVecExpr
    if acc = [] then
      (*we ignore the "c" parameter initially*)
      unroll_crc32 initial_state c' [generate_crc32 initial_state c']
    else
      if List.length acc = int buf_and_shreg_width then
        let crc =
          ctxt.MkExtract(c.SortSize - max_length_bitwidth - buf_and_shreg_width - uint32 1, uint32 0, c)
        (crc :> Expr, ctxt.MkAnd (Array.ofList acc))
      else unroll_crc32 initial_state c' (generate_crc32 c c' :: acc)

  /// <summary>Generate specification of the CRC algorithm to work within the given parameters.</summary>
  /// <param name="pre_frame">Frame excluding the FCS or trailer -- that will be filled in by the result of the CRC algorithm.</param>
  member this.specify (pre_frame : BitVecExpr) : Expr * BoolExpr =
    assert (pre_frame.SortSize = buf_width)
    (*Zero-extend a pre-frame by the width of the CRC, then shift; this gives a complete
      frame but with the CRC zeroed-out.
      pre-frame consists of header + payload; it is a frame without the trailer. The trailer is what the CRC algorithm will produce.*)
    let pre_crc_frame =
      ctxt.MkBVSHL(ctxt.MkZeroExt(crc_width, pre_frame),
                   ctxt.MkBV(crc_width, crc_width + buf_width))
    unroll_crc32
      (init_crc32_state pre_crc_frame)
      (ctxt.MkBV (0, 1u)) []

let rec crc32 (buff : bool list) (crc_shreg : uint32) : uint32 =
  let crc_width = 32 (*size of uint32*)
  let polynomial_powers = [0; 2; 4; 5; 7; 8; 10; 11; 12; 16; 22; 23; 26] (*This polynomial is mandated by the Ethernet standard*)
  match buff with
  | [] -> crc_shreg
  | b :: bs ->
      let buff_msb = if b then 1u else 0u
      let crc_reg_msb =
        (crc_shreg &&& (1u <<< (crc_width - 1)) >>> (crc_width - 1))
      let crc_shreg' = (crc_shreg <<< 1) ||| buff_msb
      List.fold (fun reg polynomial_degree ->
        reg ||| ((reg &&& (1u <<< polynomial_degree)) ^^^ (crc_reg_msb <<< polynomial_degree)))
        crc_shreg' polynomial_powers
      |> crc32 bs

(*FIXME this function is sensitive to whitespace.
        this could be fixed by trimming at the right places.*)
let string_to_mac_address (ctxt : Context) (s : string) : BitVecExpr * BoolExpr =
  let colon_sepped = s.Split [|':'|]
  let space_sepped = s.Split [|' '|]
  let bytes : string[] =
    if Array.length colon_sepped = 6 then
      colon_sepped
    else if Array.length space_sepped = 6 then
      space_sepped
    else failwith ("Unrecognised MAC address: " + s)
  interpretation_skeleton ctxt bytes
    (interpret_octet true ctxt (fun s -> System.Byte.Parse(s, System.Globalization.NumberStyles.HexNumber)))
  

(*FIXME should padding be added manually by me outside the solver?*)
(*FIXME is all checking for impossibilities to be done by the solver, 
        or should i expect that some of this is done externally?
        (e.g., if my mtu is x, the payload is y, and y > x, then return a fail).
*)
(*NOTE i avoid having members like this:
    member this.source_address
      with get () = _source_address
      and set (value) = _source_address <- value
  Other libraries have this, but it's simply a special case of the kinds of constraints that can be expressed on packets
  using my library; so I rely on the "constrain" function as the means to express all sorts of constraints, including equality.
*)
(*
FIXME currently i'm always generating frame_sz-sized frames.
      Preferebly I'd have an MTU and generate frames up to that size.
      To do that, i need a function that will generate payload sizes
      such that frame_sz = payload+header+trailer <= mtu.
*)
(* NOTE
   I think there's no need for calculating relative and absolute offsets
   (wrt encapsulating type) in the mode i'm working in, since each layer
   can create its slab of bits without caring where they will be located
   in the final frame.
*)
type ethernet (pdu_in_bytes : uint32) = (*pdu is expressed in bytes*)
  inherit constrainable_payload_carrier ()
  do
    (*The PDU, minimum MTU, or "frame size" for ethernet is 60
      bytes -- or 64 bytes if we include fcs*)
    assert (pdu_in_bytes >= uint32 64)
  let ctxt = base.context
  let slv = base.solver

(* NOTE to keep things simple i fuse these field definitions
        within those used for the backend solver. One could
        generalise the approach to work with arbitrary backends
        but i don't do that for now.
  let mutable _source_address = None
  let mutable _destination_address = None
  let mutable _ethertype = None
  let mutable _payload = None
  let mutable _fcs = None*)

  (*These sizes are fixed, or calculable from the pdu in the case of payload_sz*)
  let src_mac_sz = 48u
  let dst_mac_sz = 48u
  let ethertype_sz = 16u
  let header_sz = src_mac_sz + dst_mac_sz + ethertype_sz

  let crc32_sz = 32u
  let trailer_sz = crc32_sz

  let payload_sz =
    (pdu_in_bytes * 8u (*since we measure PDU in bytes*)) - (header_sz + trailer_sz)
  let pdu_in_bits =
    let frame_sz = header_sz + payload_sz + trailer_sz
    assert (uint32 frame_sz = pdu_in_bytes * 8u)
    frame_sz

  (*Formalise the PDU definition*)
  let dst_mac_bv = ctxt.MkBVConst ("dst_mac", dst_mac_sz)
  let src_mac_bv = ctxt.MkBVConst ("src_mac", src_mac_sz)
  let ethertype_bv = ctxt.MkBVConst ("ethertype", ethertype_sz)
  let payload_bv = ctxt.MkBVConst ("payload", payload_sz)
  let crc32_bv = ctxt.MkBVConst ("crc32", crc32_sz)

  override this.distinguished_constants =
    [(*FIXME might need to add the "ethernet." prefix*)
      { name = "source_address";
        width = uint32 src_mac_sz;
        typ = Field (src_mac_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "destination_address";
        width = uint32 dst_mac_sz;
        typ = Field (dst_mac_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "ethertype";
        width = uint32 ethertype_sz;
        typ = Field (ethertype_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "payload";
        width = uint32 payload_sz;
        typ = Field (payload_bv, I(*FIXME*));
      };
(* NOTE Since this is being computed externally to the solver, and after the solver is called,
        then the user is not allowed to make constraints on its values.
      { name = "fcs";
        width = uint32 crc32_sz;
        typ = Field (crc32_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };
*)
      { name = "mac_address";
        width =
          assert (src_mac_sz = dst_mac_sz)
          uint32 src_mac_sz;
        typ = Interpretation string_to_mac_address;
      };
      (*FIXME add the various constants for "ethertype"*)
      { name = "ethertype_ipv4";
        width = uint32 ethertype_sz;
        typ = Literal (ctxt.MkBV(0x0800u, uint32 ethertype_sz));
      };
      { name = "ethertype_arp";
        width = uint32 ethertype_sz;
        typ = Literal (ctxt.MkBV(0x0806u, uint32 ethertype_sz));
      };
      { name = "ethertype_ipv6";
        width = uint32 ethertype_sz;
        typ = Literal (ctxt.MkBV(0x86DD, uint32 ethertype_sz));
      };
    ]

  interface address_carrier with
    member this.address_width = 6uy
    member this.address_interpretation = string_to_mac_address

  (*This is the composition of the packet as constants, and doesn't contain
    actual field values.
    (It could, but I don't do that.)*)
  override this.packet_bv =
    let frame_bv =
      concat_bvs this.context [dst_mac_bv; src_mac_bv; ethertype_bv; payload_bv] // NOTE excluding crc32_bv since it's calculated rather than generated, and this this.packet_bv is used to generate packets, the solver might be changing irrelevant parts of the packet.
    assert (frame_bv.SortSize = uint32 pdu_in_bits)
    frame_bv

  override this.packet_size : uint32 = uint32 pdu_in_bits

  (*Concat together the field values we extract from a solution to
    this packet's constraints.*)
  member this.extract_packet_unchecksummed () =
    if this.solution = None then None
    else
      let extracted_packet_fields =
        ["destination_address";
         "source_address";
         "ethertype";
         "payload";
         "fcs"]
      let raw_field_extracts =
        List.map (fun fieldname ->
         (fieldname, this.extract_field_value fieldname))
         extracted_packet_fields
      List.iter (fun (fieldname, extract) ->
        if extract = None then
          failwith ("Model was found, but Ethernet field " + fieldname + " turned up null")
        else ()
      ) raw_field_extracts
      let bytes =
        List.map (snd >> Option.get) raw_field_extracts
        |> Array.concat
      if Array.length bytes * 8 > int this.packet_size then
        failwith ("Output packet size (" + string(Array.length bytes * 8) + ") exceeded PDU size (" + string(this.packet_size) + ")")
      Some bytes

  override this.extract_packet () =
    match this.extract_packet_unchecksummed () with
    | None -> None
    | Some bytes ->
(* FIXME disabled
        let frame_size = int32(header_sz + payload_sz) / 8
        let padded_bytes =
            (*In case the stated PDU is larger than what has been generated
              FIXME not sure if this is a hack or is actually needed, but it's currently needed*)
            if Array.length bytes < frame_size then
              Array.concat [bytes; Array.create (frame_size - Array.length bytes) (byte 0)]
            else
              bytes
        let frame =
            Array.sub padded_bytes 0 frame_size
            |> bytes_to_boollist
            |> List.rev
        let padding =
            let l = List.length frame % 32
            if l = 0 then []
            else
              enumerate_j 1 l
              |> List.map (fun _ -> false)
        let preprocessed =
            List.fold (fun (n, l) b ->
                let n' = n + 1
                if n < 32 then
                    (n', not b :: l)
                else
                    (n', b :: l))
              (0, []) (List.concat [frame; padding])
            |> snd
            |> List.rev
        let checksum =
          crc32 preprocessed 0u
          |> System.BitConverter.GetBytes
          |> process_bytes config.solver_is_big_endian false
        assert(Array.length checksum = 4)
        Array.set bytes frame_size checksum.[0]
        Array.set bytes (frame_size + 1) checksum.[1]
        Array.set bytes (frame_size + 2) checksum.[2]
        Array.set bytes (frame_size + 3) checksum.[3]
*)
        Some bytes

  override this.extract_field_value (field : string) : byte[] option =
    (*FIXME DRY principle with extract_packet*)
    if this.solution = None then None
    else
      (*We compute the CRC32 code after having obtained solutions for other fields*)
      match field with
      | "fcs" ->  Some [|0uy; 0uy; 0uy; 0uy|]
(* FIXME disabled
        let field_extracts =
          [this.extract_field_value "destination_address";
           this.extract_field_value "source_address";
           this.extract_field_value "ethertype";
           this.extract_field_value "payload"
           ]
          |> List.map Option.get
          |> Array.concat
          |> bytes_to_boollist
        crc32 field_extracts 0u
        |> System.BitConverter.GetBytes
        |> process_bytes config.solver_is_big_endian false
        |> Some
*)
      | "payload" ->
         match this.encapsulated_packet with
         | None -> base.extract_field_value field
         | Some (pckt : packet) ->
            ignore(pckt.generate ())
            pckt.extract_packet ()
      | _ -> base.extract_field_value field

  override this.pre_generate () =
    match this.encapsulated_packet with
    | None -> true
    | Some pckt -> pckt.generate ()

  (*Coercion placeholder from strings into an IP address*)
  static member mac_address _ (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  (*Placeholder for packet fields*)
  static member source_address (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member destination_address (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member ethertype (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member payload (*: packet_constant*) = failwith "This value should not be evaluated by F#"
(*NOTE fcs not constrainable by programmer since it's calculated based on the frame's contents
  static member fcs : packet_constant = failwith "This value should not be evaluated by F#"*)

  (*Would be nice to package all of these up under an enumerate type,
    rather than rely on their prefix to suggest that they're related.*)
  static member ethertype_ipv4 (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member ethertype_arp (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member ethertype_ipv6 (*: packet_constant*) = failwith "This value should not be evaluated by F#"
