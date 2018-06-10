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

module arp

open general
open packets
open Microsoft.Z3
open interpretation
open ir_processing

type arp<'P1, 'P2
          when 'P1 :> packet and 'P1 :> address_carrier
          and 'P2 :> packet and 'P2 :> address_carrier>
        (hp : 'P1, pp : 'P2) =
  inherit constrainable_payload_carrier () (*FIXME ARP doesn't carry a payload, so this class should be sufficient*)
  let ctxt = base.context
  let slv = base.solver

  let field_HTYPE_sz = 16u
  let field_PTYPE_sz = 16u
  let field_HLEN_sz = 8u
  let field_PLEN_sz = 8u
  let field_OPER_sz = 16u

  let field_SHA_sz = uint32 ((hp :> address_carrier).address_width) * 8u
  let field_SPA_sz = uint32 ((pp :> address_carrier).address_width) * 8u
  let field_THA_sz = uint32 ((hp :> address_carrier).address_width) * 8u
  let field_TPA_sz = uint32 ((pp :> address_carrier).address_width) * 8u

  (*Formalise the PDU definition*)
  let field_HTYPE_bv = ctxt.MkBVConst ("HTYPE", field_HTYPE_sz)
  let field_PTYPE_bv = ctxt.MkBVConst ("PTYPE", field_PTYPE_sz)
  let field_HLEN_bv = ctxt.MkBVConst ("HLEN", field_HLEN_sz)
  let field_PLEN_bv = ctxt.MkBVConst ("PLEN", field_PLEN_sz)
  let field_OPER_bv = ctxt.MkBVConst ("OPER", field_OPER_sz)
  let field_SHA_bv = ctxt.MkBVConst ("SHA", field_SHA_sz)
  let field_SPA_bv = ctxt.MkBVConst ("SPA", field_SPA_sz)
  let field_THA_bv = ctxt.MkBVConst ("THA", field_THA_sz)
  let field_TPA_bv = ctxt.MkBVConst ("TPA", field_TPA_sz)

  override this.extract_packet () =
    if this.solution = None then None
    else
      let raw_field_extracts =
        [this.extract_field_value "HTYPE";
         this.extract_field_value "PTYPE";
         this.extract_field_value "HLEN";
         this.extract_field_value "PLEN";
         this.extract_field_value "OPER";
         this.extract_field_value "SHA";
         this.extract_field_value "SPA";
         this.extract_field_value "THA";
         this.extract_field_value "TPA";
         ]
      List.map Option.get raw_field_extracts
      |> Array.concat
      |> Some

  override this.distinguished_constants =
    [{ name = "HTYPE";
       width = field_HTYPE_sz;
       typ = Field (field_HTYPE_bv, process_bytes config.solver_is_big_endian false);
     };
     { name = "PTYPE";
       width = field_PTYPE_sz;
       typ = Field (field_PTYPE_bv, process_bytes config.solver_is_big_endian false);
     };
     { name = "HLEN";
       width = field_HLEN_sz;
       typ = Field (field_HLEN_bv, process_bytes config.solver_is_big_endian false);
     };
     { name = "PLEN";
       width = field_PLEN_sz;
       typ = Field (field_PLEN_bv, process_bytes config.solver_is_big_endian false);
     };

     { name = "OPER";
       width = field_OPER_sz;
       typ = Field (field_OPER_bv, process_bytes config.solver_is_big_endian false);
     };
     { name = "SHA";
       width = field_SHA_sz;
       typ = Field (field_SHA_bv, process_bytes config.solver_is_big_endian false);
     };
     { name = "SPA";
       width = field_SPA_sz;
       typ = Field (field_SPA_bv, process_bytes config.solver_is_big_endian false);
     };
     { name = "THA";
       width = field_THA_sz;
       typ = Field (field_THA_bv, process_bytes config.solver_is_big_endian false);
     };
     { name = "TPA";
       width = field_TPA_sz;
       typ = Field (field_TPA_bv, process_bytes config.solver_is_big_endian false);
     };

     { name = "hardware_address";
       width =
         assert (field_SHA_sz = field_THA_sz)
         field_SHA_sz;
       typ = Interpretation ((hp :> address_carrier).address_interpretation);
     };
     { name = "protocol_address";
       width =
         assert (field_SPA_sz = field_TPA_sz)
         field_SPA_sz;
       typ = Interpretation ((pp :> address_carrier).address_interpretation);
     };

     (*FIXME add the various constants for "PTYPE" and "HTYPE"*)
     { name = "PTYPE_ipv4";
       width = field_PTYPE_sz;
       typ = Literal (ctxt.MkBV(0x0800u, field_PTYPE_sz));
     };
     { name = "HTYPE_ethernet";
       width = field_HTYPE_sz;
       typ = Literal (ctxt.MkBV(0x0001u, field_PTYPE_sz));
     };
     { name = "OPER_Request";
       width = field_OPER_sz;
       typ = Literal (ctxt.MkBV(0x0001u, field_OPER_sz));
     };
     { name = "OPER_Reply";
       width = field_OPER_sz;
       typ = Literal (ctxt.MkBV(0x0002u, field_OPER_sz));
     };
    ]

  override this.packet_bv =
    concat_bvs this.context
      [field_HTYPE_bv;
       field_PTYPE_bv;
       field_HLEN_bv;
       field_PLEN_bv;
       field_OPER_bv;
       field_SHA_bv;
       field_SPA_bv;
       field_THA_bv;
       field_TPA_bv]

  override this.packet_size : uint32 =
    field_HTYPE_sz +
    field_PTYPE_sz +
    field_HLEN_sz +
    field_PLEN_sz +
    field_OPER_sz +
    field_SHA_sz +
    field_SPA_sz +
    field_THA_sz +
    field_TPA_sz

  (*FIXME obtain value for payload from encapsulated packets*)
  override this.pre_generate () = true

  (*Mappers*)
  static member hardware_address _ = failwith "This value should not be evaluated by F#"
  static member protocol_address _ = failwith "This value should not be evaluated by F#"
  (*Fields*)
  static member HTYPE : 'a = failwith "This value should not be evaluated by F#"
  static member PTYPE : 'a = failwith "This value should not be evaluated by F#"
  static member HLEN : int = failwith "This value should not be evaluated by F#"
  static member PLEN : int = failwith "This value should not be evaluated by F#"
  static member OPER : 'a = failwith "This value should not be evaluated by F#"
  (*Constants*)
  static member PTYPE_ipv4 = failwith "This value should not be evaluated by F#"
  static member HTYPE_ethernet = failwith "This value should not be evaluated by F#"
  static member OPER_Request : 'a = failwith "This value should not be evaluated by F#"
  static member OPER_Reply : 'a = failwith "This value should not be evaluated by F#"
