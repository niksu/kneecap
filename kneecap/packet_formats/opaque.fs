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

module opaque

open general
open packets
open Microsoft.Z3
open interpretation
open ir_processing

/// <summary>Packet scheme generator for opaque payloads.</summary>
/// <param name="min_size">Minimum size (in bytes) of packets.</param>
/// <param name="max_size">Maximum size (in bytes) of packets.</param>
/// <param name="size_generator">Generates size (in bytes) of packets, within min_size and max_size inclusive.</param>
/// <remarks>This is based on <see cref="ipv4">ipv4</see>.</remarks>
type opaque (pdu_in_bytes : uint32) =
  inherit constrainable_payload_carrier ()
  do
    assert (pdu_in_bytes >= uint32 20(*FIXME arbitrary*))
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

  let payload_sz = pdu_in_bytes * 8u
  let pdu_in_bits = payload_sz

  (*Formalise the PDU definition*)
  let field_Payload_bv = ctxt.MkBVConst ("field_Opaque_Payload_bv"(*FIXME need to ensure names from different packet formats don't collide?*), payload_sz)

  override this.extract_field_value (field : string) : byte[] option =
    if this.solution = None then None
    else
      match field with
      | "payload" -> base.extract_field_value field
      | _ -> failwith ("Field not supported: " + field)

  override this.distinguished_constants =
    [ { name = "payload";
        width = payload_sz;
        typ = Field (field_Payload_bv, process_bytes config.solver_is_big_endian false);
      }]

  override this.packet_bv =
    let frame_bv = field_Payload_bv
    assert (frame_bv.SortSize = uint32 pdu_in_bits)
    frame_bv

  (*override this.remove_encapsulated_packet () = failwith "Cannot remove_encapsulated_packet"*)
  override this.packet_size : uint32 = uint32 pdu_in_bits

  (*Concat together the field values we extract from a solution to
    this packet's constraints.*)
  override this.extract_packet () =
    if this.solution = None then None
    else
      let raw_field_extracts = [this.extract_field_value "payload"]
      let bytes =
        List.map Option.get raw_field_extracts
        |> Array.concat
      if Array.length bytes * 8 > int this.packet_size then
        failwith "Output packet size exceeded PDU size"
      Some bytes

  override this.pre_generate () = true
