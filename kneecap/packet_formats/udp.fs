(*
   Copyright 2018 Nik Sultana

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

module udp

open general
open packets
open Microsoft.Z3
open interpretation
open ir_processing

/// <summary>Packet scheme generator for UDP.</summary>
/// <param name="min_size">Minimum size (in bytes) of packets.</param>
/// <param name="max_size">Maximum size (in bytes) of packets.</param>
/// <param name="size_generator">Generates size (in bytes) of packets, within min_size and max_size inclusive.</param>
/// <remarks>This is based on <see cref="ipv4">ipv4</see>.</remarks>
type udp (pdu_in_bytes : uint32) =
  inherit constrainable_payload_carrier ()
  do
    assert (pdu_in_bytes >= uint32 8)
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
  let field_Length_sz = 16u
  let field_Checksum_sz = 16u

  let header_sz =
    field_SourcePort_sz +
    field_DestinationPort_sz +
    field_Length_sz +
    field_Checksum_sz

  let payload_sz =
    (pdu_in_bytes * 8u) - header_sz
  let pdu_in_bits = header_sz + payload_sz

  (*Formalise the PDU definition*)

  let field_SourcePort_bv = ctxt.MkBVConst ("field_SourcePort", field_SourcePort_sz)
  let field_DestinationPort_bv = ctxt.MkBVConst ("field_DestinationPort", field_DestinationPort_sz)
  let field_Length_bv = ctxt.MkBVConst ("field_Length", field_Length_sz)
  let field_Checksum_bv = ctxt.MkBVConst ("field_Checksum", field_Checksum_sz)

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
    [ { name = "source_port";
        width = field_SourcePort_sz;
        typ = Field (field_SourcePort_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "destination_port";
        width = field_DestinationPort_sz;
        typ = Field (field_DestinationPort_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "length";
        width = field_Length_sz;
        typ = Field (field_Length_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "checksum";
        width = field_Checksum_sz;
        typ = Field (field_Checksum_bv, process_bytes config.solver_is_big_endian false);
      };
    ]

  override this.packet_bv =
    let frame_bv =
      concat_bvs this.context
        [field_SourcePort_bv;
         field_DestinationPort_bv;
         field_Length_bv;
         field_Checksum_bv]
    assert (frame_bv.SortSize = uint32 pdu_in_bits)
    frame_bv

(*  override this.remove_encapsulated_packet () = ()*)
  override this.packet_size : uint32 = uint32 pdu_in_bits

  (*Concat together the field values we extract from a solution to
    this packet's constraints.*)
  member this.extract_packet_unchecksummed () =
    if this.solution = None then None
    else
      let raw_field_extracts = [
         this.extract_field_value "source_port";
         this.extract_field_value "destination_port";
         this.extract_field_value "length";
         this.extract_field_value "checksum";
         this.extract_field_value "payload";
         ]
      let bytes =
        List.map Option.get raw_field_extracts
        |> Array.concat
      if Array.length bytes * 8 > int this.packet_size then
        failwith "Output packet size exceeded PDU size"
      Some bytes

  override this.extract_packet () =
    match this.extract_packet_unchecksummed () with
    | None -> None
    | Some bytes ->
        (*FIXME add pseudoheader -- how to reference packet container?*)
        (*FIXME ensure have even number of bytes -- padding*)
        let b1, b2 = ipv4.ipv4.checksum bytes
        Array.set bytes 7 b1
        Array.set bytes 8 b2
        Some bytes

  override this.pre_generate () =
    match this.encapsulated_packet with
    | None -> true
    | Some pckt -> pckt.generate ()

  (*Placeholder for packet fields*)
  static member payload (*: packet_constant*) = failwith "This value should not be evaluated by F#"

  static member source_port : int (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member destination_port : int (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member length (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member checksum (*: packet_constant*) = failwith "This value should not be evaluated by F#"
