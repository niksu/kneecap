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

// FIXME so far this implementation is only a sketch. More refining needed.
module tcp // NOTE the protocol spec is at: https://tools.ietf.org/html/rfc793

open general
open packets
open Microsoft.Z3
open interpretation
open ir_processing

/// <summary>Packet scheme generator for TCPv4.</summary>
/// <param name="min_size">Minimum size (in bytes) of packets.</param>
/// <param name="max_size">Maximum size (in bytes) of packets.</param>
/// <param name="size_generator">Generates size (in bytes) of packets, within min_size and max_size inclusive.</param>
/// <remarks>This is based on <see cref="ipv4">ipv4</see>.</remarks>
type tcp (pdu_in_bytes : uint32) =
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
  let field_SourcePort_sz = 16u
  let field_DestinationPort_sz = 16u
  let field_SeqNo_sz = 32u
  let field_AckNo_sz = 32u
  let field_DataOffset_sz = 4u
  let field_Reserved_sz = 3u
  let field_Flag_NS_sz = 1u
  let field_Flag_CWR_sz = 1u
  let field_Flag_ECE_sz = 1u
  let field_Flag_URG_sz = 1u
  let field_Flag_ACK_sz = 1u
  let field_Flag_PSH_sz = 1u
  let field_Flag_RST_sz = 1u
  let field_Flag_SYN_sz = 1u
  let field_Flag_FIN_sz = 1u
  let field_WindowSize_sz = 16u
  let field_Checksum_sz = 16u
  let field_UrgentPointer_sz = 16u
  let field_Options_sz = 0u (*FIXME unsupported*)

  let header_sz =
    field_SourcePort_sz +
    field_DestinationPort_sz +
    field_SeqNo_sz +
    field_AckNo_sz +
    field_DataOffset_sz +
    field_Reserved_sz +
    field_Flag_NS_sz +
    field_Flag_CWR_sz +
    field_Flag_ECE_sz +
    field_Flag_URG_sz +
    field_Flag_ACK_sz +
    field_Flag_PSH_sz +
    field_Flag_RST_sz +
    field_Flag_SYN_sz +
    field_Flag_FIN_sz +
    field_WindowSize_sz +
    field_Checksum_sz +
    field_UrgentPointer_sz +
    field_Options_sz

  let payload_sz =
    (pdu_in_bytes * 8u) - header_sz
  let pdu_in_bits = header_sz + payload_sz

  (*Formalise the PDU definition*)

  let field_SourcePort_bv = ctxt.MkBVConst ("field_SourcePort", field_SourcePort_sz)
  let field_DestinationPort_bv = ctxt.MkBVConst ("field_DestinationPort", field_DestinationPort_sz)
  let field_SeqNo_bv = ctxt.MkBVConst ("field_SeqNo", field_SeqNo_sz)
  let field_AckNo_bv = ctxt.MkBVConst ("field_AckNo", field_AckNo_sz)
  let field_DataOffset_bv = ctxt.MkBVConst ("field_DataOffset", field_DataOffset_sz)
  let field_Reserved_bv = ctxt.MkBVConst ("field_Reserved", field_Reserved_sz)
  let field_Flag_NS_bv = ctxt.MkBVConst ("field_Flag_NS", field_Flag_NS_sz)
  let field_Flag_CWR_bv = ctxt.MkBVConst ("field_Flag_CWR", field_Flag_CWR_sz)
  let field_Flag_ECE_bv = ctxt.MkBVConst ("field_Flag_ECE", field_Flag_ECE_sz)
  let field_Flag_URG_bv = ctxt.MkBVConst ("field_Flag_URG", field_Flag_URG_sz)
  let field_Flag_ACK_bv = ctxt.MkBVConst ("field_Flag_ACK", field_Flag_ACK_sz)
  let field_Flag_PSH_bv = ctxt.MkBVConst ("field_Flag_PSH", field_Flag_PSH_sz)
  let field_Flag_RST_bv = ctxt.MkBVConst ("field_Flag_RST", field_Flag_RST_sz)
  let field_Flag_SYN_bv = ctxt.MkBVConst ("field_Flag_SYN", field_Flag_SYN_sz)
  let field_Flag_FIN_bv = ctxt.MkBVConst ("field_Flag_FIN", field_Flag_FIN_sz)
  let field_WindowSize_bv = ctxt.MkBVConst ("field_WindowSize", field_WindowSize_sz)
  let field_Checksum_bv = ctxt.MkBVConst ("field_Checksum", field_Checksum_sz)
  let field_UrgentPointer_bv = ctxt.MkBVConst ("field_UrgentPointer", field_UrgentPointer_sz)
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
            pckt.generate ()
            pckt.extract_packet ()
      | _ -> base.extract_field_value field

  override this.distinguished_constants =
    [ { name = "source_port";
        width = field_SourcePort_sz;
        typ = Field (field_SourcePort_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "destination_port";
        width = field_DestinationPort_sz;
        typ = Field (field_DestinationPort_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "sequence_number";
        width = field_SeqNo_sz;
        typ = Field (field_SeqNo_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "acknowledgement_number";
        width = field_AckNo_sz;
        typ = Field (field_AckNo_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "data_offset";
        width = field_DataOffset_sz;
        typ = Field (field_DataOffset_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "reserved";
        width = field_Reserved_sz;
        typ = Field (field_Reserved_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "NS";
        width = field_Flag_NS_sz;
        typ = Field (field_Flag_NS_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "CWR";
        width = field_Flag_CWR_sz;
        typ = Field (field_Flag_CWR_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "ECE";
        width = field_Flag_ECE_sz;
        typ = Field (field_Flag_ECE_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "URG";
        width = field_Flag_URG_sz;
        typ = Field (field_Flag_URG_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "ACK";
        width = field_Flag_ACK_sz;
        typ = Field (field_Flag_ACK_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "PSH";
        width = field_Flag_PSH_sz;
        typ = Field (field_Flag_PSH_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "RST";
        width = field_Flag_RST_sz;
        typ = Field (field_Flag_RST_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "SYN";
        width = field_Flag_SYN_sz;
        typ = Field (field_Flag_SYN_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "FIN";
        width = field_Flag_FIN_sz;
        typ = Field (field_Flag_FIN_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "window_size";
        width = field_WindowSize_sz;
        typ = Field (field_WindowSize_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "checksum";
        width = field_Checksum_sz;
        typ = Field (field_Checksum_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "urgent_pointer";
        width = field_UrgentPointer_sz;
        typ = Field (field_UrgentPointer_bv, process_bytes config.solver_is_big_endian false);
      };

      { name = "payload";
        width = payload_sz;
        typ = Field (field_payload_bv, I(*FIXME*));
      };

      (*FIXME make abbreviated syntax for bools, so can say "tcp.FIN" instead of "tcp.FIN = 1"?*)
    ]

  override this.packet_bv =
    let frame_bv =
      concat_bvs this.context
        [field_SourcePort_bv;
         field_DestinationPort_bv;
         field_SeqNo_bv;
         field_AckNo_bv;
         field_DataOffset_bv;
         field_Reserved_bv;
         field_Flag_NS_bv;
         field_Flag_CWR_bv;
         field_Flag_ECE_bv;
         field_Flag_URG_bv;
         field_Flag_ACK_bv;
         field_Flag_PSH_bv;
         field_Flag_RST_bv;
         field_Flag_SYN_bv;
         field_Flag_FIN_bv;
         field_WindowSize_bv;
         field_Checksum_bv;
         field_UrgentPointer_bv;
         field_payload_bv]
    assert (frame_bv.SortSize = uint32 pdu_in_bits)
    frame_bv

(*  override this.remove_encapsulated_packet () = ()*)
  override this.packet_size : uint32 = uint32 pdu_in_bits

  (*Concat together the field values we extract from a solution to
    this packet's constraints.*)
  override this.extract_packet () =
    if this.solution = None then None
    else
      let raw_field_extracts =
        [(*FIXME use this.extract_concatted_field_values for some fields?*)
         this.extract_field_value "source_port";
         this.extract_field_value "destination_port";
         this.extract_field_value "sequence_number";
         this.extract_field_value "acknowledgement_number";
         this.extract_field_value "data_offset";
         this.extract_field_value "reserved";
         this.extract_field_value "NS";
         this.extract_field_value "CWR";
         this.extract_field_value "ECE";
         this.extract_field_value "URG";
         this.extract_field_value "ACK";
         this.extract_field_value "PSH";
         this.extract_field_value "RST";
         this.extract_field_value "SYN";
         this.extract_field_value "FIN";
         this.extract_field_value "window_size";
         this.extract_field_value "checksum";
         this.extract_field_value "urgent_pointer";
         this.extract_field_value "payload";
         ]
      let bytes =
        List.map Option.get raw_field_extracts
        |> Array.concat
      if Array.length bytes * 8 > int this.packet_size then
        failwith "Output packet size exceeded PDU size"
      Some bytes

  (*FIXME obtain value for payload from encapsulated packets*)
  override this.pre_generate () = true

  (*Placeholder for packet fields*)
  static member payload (*: packet_constant*) = failwith "This value should not be evaluated by F#"

  static member source_port (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member destination_port (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member sequence_number (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member acknowledgement_number (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member data_offset (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member reserved (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member NS (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member CWR (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member ECE (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member URG (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member ACK (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member PSH (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member RST (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member SYN (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member FIN (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member window_size (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member checksum (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member urgent_pointer (*: packet_constant*) = failwith "This value should not be evaluated by F#"
