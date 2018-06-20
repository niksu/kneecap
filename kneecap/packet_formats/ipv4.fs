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

module ipv4

open general
open packets
open Microsoft.Z3
open interpretation
open ir_processing

(*NOTE this is based on ethernet.string_to_mac_address*)
let string_to_ipv4_address (ctxt : Context) (s : string) : BitVecExpr * BoolExpr =
  let bytes : string[] =
    let dot_sepped = s.Split [|'.'|]
    assert (Array.length dot_sepped = 4)
    dot_sepped
  interpretation_skeleton ctxt bytes
   (interpret_octet true ctxt (fun s -> System.Byte.Parse(s, System.Globalization.NumberStyles.Integer)))



/// <summary>Packet scheme generator for IPv4.</summary>
/// <param name="min_size">Minimum size (in bytes) of packets.</param>
/// <param name="max_size">Maximum size (in bytes) of packets.</param>
/// <param name="size_generator">Generates size (in bytes) of packets, within min_size and max_size inclusive.</param>
/// <remarks>This is based on <see cref="ethernet">ethernet</see>.</remarks>
type ipv4 (pdu_in_bytes : uint32) =
  inherit constrainable_payload_carrier ()
  do
    assert (pdu_in_bytes >= uint32 20)
  let ctxt = base.context
  let slv = base.solver

(*
  NOTE instead of using a function to generate new sizes, i'm relying on
       the encapsulated packet to implicitly constrain the total length
       by the size of the payload it generates.
  (*NOTE total_length cannot be constrained in the language -- it's constrained by min_size, max_size, and the definition of size_generator*)
  let generate_new_size () : uint32 =
    let newsize = size_generator ()
    assert (min_size <= newsize)
    assert (max_size >= newsize)
    newsize
*)

  (*These sizes are fixed, or calculable from the pdu in the case of payload_sz*)
  let field_Version_sz = 4u
  let field_IHL_sz = 4u
  let field_DSCP_sz = 6u
  let field_ECN_sz = 2u
  let field_Total_Length_sz = 16u
  let field_Identification_sz = 16u
  let field_Flags_sz = 3u
  let field_Fragment_Offset_sz = 13u
  let field_Time_To_Live_sz = 8u
  let field_Protocol_sz = 8u
  let field_Header_Checksum_sz = 16u
  let field_Source_IP_Address_sz = 32u
  let field_Destination_IP_Address_sz = 32u
  let field_Options_sz = 0u (*FIXME unsupported*)

  let header_sz =
    field_Version_sz +
    field_IHL_sz +
    field_DSCP_sz +
    field_ECN_sz +
    field_Total_Length_sz +
    field_Identification_sz +
    field_Flags_sz +
    field_Fragment_Offset_sz +
    field_Time_To_Live_sz +
    field_Protocol_sz +
    field_Header_Checksum_sz +
    field_Source_IP_Address_sz +
    field_Destination_IP_Address_sz +
    field_Options_sz

  let payload_sz =
    (pdu_in_bytes * 8u) - header_sz
  let pdu_in_bits = header_sz + payload_sz

  (*Formalise the PDU definition*)

  let field_Version_bv = ctxt.MkBVConst ("field_Version", field_Version_sz)
  let field_IHL_bv = ctxt.MkBVConst ("field_IHL", field_IHL_sz)
  let field_DSCP_bv = ctxt.MkBVConst ("field_DSCP", field_DSCP_sz)
  let field_ECN_bv = ctxt.MkBVConst ("field_ECN", field_ECN_sz)
  let field_Total_Length_bv = ctxt.MkBVConst ("field_Total_Length", field_Total_Length_sz)
  let field_Identification_bv = ctxt.MkBVConst ("field_Identification", field_Identification_sz)
  let field_Flags_bv = ctxt.MkBVConst ("field_Flags", field_Flags_sz)
  let field_Fragment_Offset_bv = ctxt.MkBVConst ("field_Fragment_Offset", field_Fragment_Offset_sz)
  let field_Time_To_Live_bv = ctxt.MkBVConst ("field_Time_To_Live", field_Time_To_Live_sz)
  let field_Protocol_bv = ctxt.MkBVConst ("field_Protocol", field_Protocol_sz)
  let field_Header_Checksum_bv = ctxt.MkBVConst ("field_Header_Checksum", field_Header_Checksum_sz)
  let field_Source_IP_Address_bv = ctxt.MkBVConst ("field_Source_IP_Address", field_Source_IP_Address_sz)
  let field_Destination_IP_Address_bv = ctxt.MkBVConst ("field_Destination_IP_Address", field_Destination_IP_Address_sz)
  (*FIXME Options field currently unsupported*)
  let field_payload_bv = ctxt.MkBVConst ("field_payload", payload_sz)

  override this.extract_field_value (field : string) : byte[] option = 
    (*FIXME DRY principle with extract_packet*)
    if this.solution = None then None
    else
      (*We compute the CRC32 code after having obtained solutions for other fields*)
      match field with
      | "header_checksum" ->
         (*calculate based on existing fields in solution, if there is one;*)
         (*FIXME*)
         Some [|0uy; 0uy|]
      | "payload" ->
         match this.encapsulated_packet with
         | None -> base.extract_field_value field
         | Some (pckt : packet) ->
            ignore(pckt.generate ())
            pckt.extract_packet ()
      | _ -> base.extract_field_value field

  override this.distinguished_constants =
    [ { name = "source_address";
        width = field_Source_IP_Address_sz;
        typ = Field (field_Source_IP_Address_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "destination_address";
        width = field_Destination_IP_Address_sz;
        typ = Field (field_Destination_IP_Address_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "protocol";
        width = field_Protocol_sz;
        typ = Field (field_Protocol_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "payload";
        width = payload_sz;
        typ = Field (field_payload_bv, I(*FIXME*));
      };

      { name = "version";
        width = field_Version_sz;
        typ = Field (field_Version_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };
      { name = "internet_header_length";
        width = field_IHL_sz;
        typ = Field (field_IHL_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };
      { name = "DSCP";
        width = field_DSCP_sz;
        typ = Field (field_DSCP_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };
      { name = "ECN";
        width = field_ECN_sz;
        typ = Field (field_ECN_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };
      { name = "total_length";
        width = field_Total_Length_sz;
        typ = Field (field_Total_Length_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };
      { name = "identification";
        width = field_Identification_sz;
        typ = Field (field_Identification_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };
      { name = "flags";
        width = field_Flags_sz;
        typ = Field (field_Flags_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };
      { name = "fragment_offset";
        width = field_Fragment_Offset_sz;
        typ = Field (field_Fragment_Offset_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };
      { name = "TTL";
        width = field_Time_To_Live_sz;
        typ = Field (field_Time_To_Live_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };

      { name = "ipv4_address";
        width =
          assert (field_Source_IP_Address_sz = field_Destination_IP_Address_sz)
          field_Source_IP_Address_sz;
        typ = Interpretation string_to_ipv4_address;
      };
      (*FIXME add the various constants for "ethertype"*)
      { name = "protocol_icmp";
        width = field_Protocol_sz;
        typ = Literal (ctxt.MkBV(0x01u, field_Protocol_sz));
      };
      { name = "protocol_ip_in_ip";
        width = field_Protocol_sz;
        typ = Literal (ctxt.MkBV(0x04u, field_Protocol_sz));
      };
      { name = "protocol_udp";
        width = field_Protocol_sz;
        typ = Literal (ctxt.MkBV(0x11u, field_Protocol_sz));
      };
      { name = "protocol_tcp";
        width = field_Protocol_sz;
        typ = Literal (ctxt.MkBV(0x06u, field_Protocol_sz));
      };
      { name = "protocol_etherip";
        width = field_Protocol_sz;
        typ = Literal (ctxt.MkBV(0x61u, field_Protocol_sz));
      };
    ]

  override this.packet_bv =
    let frame_bv =
      concat_bvs this.context
        [field_Version_bv;
         field_IHL_bv;
         field_DSCP_bv;
         field_ECN_bv;
         field_Total_Length_bv;
         field_Identification_bv;
         field_Flags_bv;
         field_Fragment_Offset_bv;
         field_Time_To_Live_bv;
         field_Protocol_bv;
         field_Header_Checksum_bv; // FIXME should exclude this, similar to how the crc32 is excluded in Ethernet?
         field_Source_IP_Address_bv;
         field_Destination_IP_Address_bv;
         field_payload_bv]
    assert (frame_bv.SortSize = uint32 pdu_in_bits)
    frame_bv

(*  override this.remove_encapsulated_packet () = ()*)
  override this.packet_size : uint32 = uint32 pdu_in_bits

  (*Concat together the field values we extract from a solution to
    this packet's constraints.*)
  member this.extract_packet_unchecksummed () =
    if this.solution = None then None
    else
      let raw_field_names =
        [["version"; "internet_header_length"];
         ["DSCP"; "ECN"];
         ["total_length"];
         ["identification"];
         ["flags"; "fragment_offset"];
         ["TTL"];
         ["protocol"];
         ["header_checksum"];
         ["source_address"];
         ["destination_address"];
         ["payload"];
         ]
      let raw_field_extracts =
        List.fold (fun st fields ->
            match fields with
            | [] -> failwith "Impossible"
            | [field] -> (fields, this.extract_field_value field) :: st
            | _ -> (fields, this.extract_concatted_field_values I(*FIXME*) fields) :: st
        ) [] raw_field_names
        |> List.rev
      List.iter (fun (fieldnames, extract) ->
        if extract = None then
          let fieldnames_str : string = String.concat ", " fieldnames
          failwith ("Model was found, but IPv4 field/s (" + fieldnames_str + ") turned up null")
          (*FIXME replace "IPv4" with a reference to a const field in this class describing this protocol.*)
        else ()
      ) raw_field_extracts
      let bytes =
        List.map snd raw_field_extracts
        |> List.map Option.get
        |> Array.concat
      if Array.length bytes * 8 > int this.packet_size then
        failwith ("Output packet size (" + string(Array.length bytes * 8) + ") exceeded PDU size (" + string(this.packet_size) + ")")
      Some bytes

  static member checksum (bs : byte[]) : byte * byte =
      let rec pair_bytes xs acc =
        match xs with
        | [] -> List.rev acc
        | [_] -> failwith "Odd number of bytes cannot be processed by checksum"
        | b1 :: b2 :: rest ->
            pair_bytes rest ((b1, b2) :: acc)
      let byte_pairs =
        pair_bytes (List.ofArray bs) []
        |> List.map (fun (b1, b2) ->
          (uint16(b1) <<< 8) + uint16(b2))
      let sum = List.fold (fun (st : uint32) (x : uint16) ->
          st + uint32(x)) 0u byte_pairs
      let added_carry : uint16 =
          let carry : uint32 = 0x000F0000u &&& sum
          uint16((0x0000FFFFu &&& sum) + carry)
      let result = ~~~ added_carry
      byte(result >>> 8), byte(result)

  override this.extract_packet () =
    match this.extract_packet_unchecksummed () with
    | None -> None
    | Some bytes ->
        let b1, b2 = ipv4.checksum (Array.sub bytes 0 (int32(header_sz) / 8))
        Array.set bytes 10 b1
        Array.set bytes 11 b2
        Some bytes

  override this.pre_generate () =
    match this.encapsulated_packet with
    | None -> true
    | Some pckt -> pckt.generate ()

  (*Coercion placeholder from strings into an IP address*)
  static member ipv4_address _ (*: packet_constant *)= failwith "This value should not be evaluated by F#"
  (*Placeholder for packet fields*)
  static member source_address (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member destination_address (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member protocol (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member payload (*: packet_constant*) = failwith "This value should not be evaluated by F#"

  (*field_Total_Length won't be exposed to users to constrain, since
    it will be constrained by whatever we are carrying -- otherwise
    it is 0.
    FIXME Or could expose it to see if we can confuse equipment and software?

    Similarly field_Header_Checksum_bv isn't exposed, since that's calculated based on the solution we got from the solver.
  *)

  (*FIXME would be nice to have "default values", so that if the user
          doesn't specify a version, then we'll set it to "4" by default.*)
  static member version : int (*: packet_constant*) = failwith "This value should not be evaluated by F#"

  static member internet_header_length : int (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member DSCP (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member ECN (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member total_length : int (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member identification (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member flags (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member fragment_offset (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member TTL : int (*: packet_constant*) = failwith "This value should not be evaluated by F#"

  (*Would be nice to package all of these up under an enumerate type,
    rather than rely on their prefix to suggest that they're related.*)
  static member protocol_icmp (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member protocol_ip_in_ip (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member protocol_udp (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member protocol_tcp (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member protocol_etherip (*: packet_constant*) = failwith "This value should not be evaluated by F#"

  interface address_carrier with
    member this.address_width = 4uy
    member this.address_interpretation = string_to_ipv4_address
