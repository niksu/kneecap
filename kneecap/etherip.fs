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

module etherip

open general
open packets
open Microsoft.Z3
open interpretation
open ir_processing

/// EtherIP packets.
/// http://tools.ietf.org/html/rfc3378
/// According to the RFC, for correct operation, version = 3, reserved = 0, and
/// the encapsulated ethernet frame shouldn't have an FCS.
type etherip (pdu_in_bytes : uint32) =
  inherit constrainable_payload_carrier ()
  do
    assert (pdu_in_bytes >= 2u(*required by etherip*) + 64u(*required by ethernet*))
  let ctxt = base.context
  let slv = base.solver

  (*These sizes are fixed, or calculable from the pdu in the case of payload_sz*)
  let field_Version_sz = 4u
  let field_Reserved_sz = 12u

  let header_sz =
    field_Version_sz +
    field_Reserved_sz

  let payload_sz =
    (pdu_in_bytes * 8u) - header_sz
  let pdu_in_bits = header_sz + payload_sz

  (*Formalise the PDU definition*)

  let field_Version_bv = ctxt.MkBVConst ("field_Version", field_Version_sz)
  let field_Reserved_bv = ctxt.MkBVConst ("field_Reserved", field_Reserved_sz)
  let field_payload_bv = ctxt.MkBVConst ("field_payload", payload_sz)

  override this.extract_field_value (field : string) : byte[] option = 
    if this.solution = None then None
    else
      match field with
      | "payload" ->
         match this.encapsulated_packet with
         | None -> base.extract_field_value field
         | Some (pckt : packet) ->
            pckt.generate ()
            pckt.extract_packet ()
      | _ -> base.extract_field_value field

  override this.distinguished_constants =
    [ { name = "version";
        width = field_Version_sz;
        typ = Field (field_Version_bv, process_bytes config.solver_is_big_endian false (*FIXME I*));
      };
      { name = "reserved";
        width = field_Reserved_sz;
        typ = Field (field_Reserved_bv, process_bytes config.solver_is_big_endian false);
      };
      { name = "payload";
        width = payload_sz;
        typ = Field (field_payload_bv, I(*FIXME*));
      };
    ]

  override this.packet_bv =
    let frame_bv =
      concat_bvs this.context
        [field_Version_bv;
         field_Reserved_bv;
         field_payload_bv]
    assert (frame_bv.SortSize = pdu_in_bits)
    frame_bv

  override this.packet_size : uint32 = pdu_in_bits

  (*Concat together the field values we extract from a solution to
    this packet's constraints.*)
  override this.extract_packet () =
    if this.solution = None then None
    else
      let raw_field_extracts =
        [this.extract_concatted_field_values 
          (process_bytes config.solver_is_big_endian false)
          ["version"; "reserved"];
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

  (*Fields*)
  static member version : int (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member reserved (*: packet_constant*) = failwith "This value should not be evaluated by F#"
  static member payload (*: packet_constant*) = failwith "This value should not be evaluated by F#"
