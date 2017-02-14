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

(* FIXME use of 'assert' in this module requires DEBUG to be set at compile
         time. should refactor for the parameter to 'assert' to have an effect
         even if the assertion isn't actually being checked.*)

module pcap

type magic_code =
  | Big_Endian    = 0xa1b2c3d4u
  | Little_Endian = 0xd4c3b2a1u

type data_link_type =
  | Ethernet = 1

(*In the file this is fixed to a 24-byte header*)
type global_header =
  { magic_number : magic_code; (*uint32*)
    version_major : uint16;
    version_minor : uint16;
    thiszone : int32;
    sigfigs : uint32; (*NOTE usually fixed to 0, following standard tools*)
    snaplen : uint32; (*NOTE by default this is 65535 in standard tools*)
    network : data_link_type
  }

(*FIXME fixed values*)
let default_global_header =
  { magic_number = magic_code.Big_Endian;
    version_major = uint16 2;
    version_minor = uint16 4;
    thiszone = 0;
    sigfigs = uint32 0;
    snaplen = uint32 65536;
    network = data_link_type.Ethernet;
  }

(*Fixed-size 16-byte header preceding a variable-length packet*)
type header =
  {  ts_sec : uint32;
     ts_usec : uint32;
     incl_len : uint32;
     orig_len : uint32;
     (*NOTE usually incl_len=orig_len unless orig_len>snaplen, in which case the packet gets truncated when stored
            in the pcap file, and therefore orig_len>incl_len*)
  }

(*We regard the data opaquely -- it's up to other modules to understand that, not up to us.*)
type data = byte[]

type pcap_file_packet =
  { header : header;
    data : data
  }

type pcap_file_contents =
  {  global_header : global_header;
     packets : pcap_file_packet list
  }

open System.IO

let serialise_pcap (filepath : string) (contents : pcap_file_contents) : unit =
  if File.Exists (filepath) then
    failwith ("File " + filepath + " already exists.")
  use fd = File.Create filepath
  let mc =
    match contents.global_header.magic_number with
    | magic_code.Little_Endian -> 0xd4c3b2a1u
    | magic_code.Big_Endian -> 0xa1b2c3d4u
    | _ -> failwith "Unsupported endianness"
  let nw =
    match contents.global_header.network with
    | data_link_type.Ethernet -> 1u
    | _ -> failwith "Unsupported data link type"
  List.iter (fun bytes -> fd.Write(bytes, 0, Array.length bytes))
    ([System.BitConverter.GetBytes(mc);
      System.BitConverter.GetBytes(contents.global_header.version_major);
      System.BitConverter.GetBytes(contents.global_header.version_minor);
      System.BitConverter.GetBytes(contents.global_header.thiszone);
      System.BitConverter.GetBytes(contents.global_header.sigfigs);
      System.BitConverter.GetBytes(contents.global_header.snaplen);
      System.BitConverter.GetBytes(nw);
     ] : byte[] list)
  List.iter
    (fun pfp ->
      List.iter
        (fun bytes ->
          fd.Write(bytes, 0, Array.length bytes))
        ([System.BitConverter.GetBytes(pfp.header.ts_sec);
          System.BitConverter.GetBytes(pfp.header.ts_usec);
          System.BitConverter.GetBytes(pfp.header.incl_len);
          System.BitConverter.GetBytes(pfp.header.incl_len);
          pfp.data;
         ] : byte[] list)) contents.packets
  fd.Close ()

let deserialise_pcap (filepath : string) : pcap_file_contents =
  if not (File.Exists (filepath)) then
    failwith ("File " + filepath + " not found.")
  use fd = File.OpenRead filepath
  let mutable pcap_contents =
    {global_header =
      { magic_number = magic_code.Big_Endian; (*default*)
        version_major = 0us;
        version_minor = 0us;
        thiszone = 0;
        sigfigs = 0u;
        snaplen = 0u;
        network = data_link_type.Ethernet; (*default*)
      };
     packets = []}

  (*Initially create the buffer large enough to hold the global header*)
  (*FIXME doesn't actually need to be this big, since global header isn't
          stored in the buffer simultaneously, as currently implemented.*)
  let buffer = Array.create (24) (byte 0)

  assert (fd.Read(buffer, 0, sizeof<uint32>) = 4)
  pcap_contents <-
    { pcap_contents
      with global_header =
           { pcap_contents.global_header
             with magic_number =
                  match System.BitConverter.ToUInt32(buffer, 0) with
                  | 0xa1b2c3d4u -> magic_code.Big_Endian
                  | 0xd4c3b2a1u -> magic_code.Little_Endian
                  | n -> failwith ("Unrecognised magic number:" ^ string n)}}

  assert (fd.Read(buffer, 0, sizeof<uint16>) = 2)
  pcap_contents <-
    { pcap_contents
      with global_header =
           { pcap_contents.global_header
             with version_major = System.BitConverter.ToUInt16(buffer, 0) }}

  assert (fd.Read(buffer, 0, sizeof<uint16>) = 2)
  pcap_contents <-
    { pcap_contents
      with global_header =
           { pcap_contents.global_header
             with version_minor = System.BitConverter.ToUInt16(buffer, 0) }}

  assert (fd.Read(buffer, 0, sizeof<int32>) = 4)
  pcap_contents <-
    { pcap_contents
      with global_header =
           { pcap_contents.global_header
             with thiszone = System.BitConverter.ToInt32(buffer, 0) }}

  assert (fd.Read(buffer, 0, sizeof<uint32>) = 4)
  pcap_contents <-
    { pcap_contents
      with global_header =
           { pcap_contents.global_header
             with sigfigs = System.BitConverter.ToUInt32(buffer, 0) }}

  assert (fd.Read(buffer, 0, sizeof<uint32>) = 4)
  pcap_contents <-
    { pcap_contents
      with global_header =
           { pcap_contents.global_header
             with snaplen = System.BitConverter.ToUInt32(buffer, 0) }}

  assert (fd.Read(buffer, 0, sizeof<uint32>) = 4)
  pcap_contents <-
    { pcap_contents
      with global_header =
           { pcap_contents.global_header
             with network =
               match System.BitConverter.ToUInt32(buffer, 0) with
               | 1u -> data_link_type.Ethernet
               | n -> failwith ("Unrecognised data_link_type value: " + string n)
           }}

  (*Buffer is now large enough to hold the header + maximum packet size*)
  let buffer = Array.create (int pcap_contents.global_header.snaplen +
    20(*FIXME not needed, since header and packet not stored in buffer simultaneously*)) (byte 0)

  (*Header preceding a packet is always 20 bytes long*)
  while (fd.Read(buffer, 0, 16) = 16) do
    let packet_header =
      { ts_sec = System.BitConverter.ToUInt32(buffer, 0);
        ts_usec = System.BitConverter.ToUInt32(buffer, 4);
        incl_len = System.BitConverter.ToUInt32(buffer, 8);
        orig_len = System.BitConverter.ToUInt32(buffer, 12) }

    let packet_data =
(* FIXME debug code
      printfn "ts_sec %d" packet_header.ts_sec
      printfn "ts_usec %d" packet_header.ts_usec
      printfn "orig_len %d" packet_header.orig_len
      printfn "reading packet of len %d" packet_header.incl_len
*)
      assert (fd.Read(buffer, 0, int packet_header.incl_len) = int packet_header.incl_len)
      let store = Array.create (int32 packet_header.incl_len) (byte 0)
      System.Buffer.BlockCopy(buffer, 0, store, 0, int32 packet_header.incl_len)
      store

    pcap_contents <-
      { pcap_contents
        with packets =
             { header = packet_header; data = packet_data } :: pcap_contents.packets }
  done
  (*Have to reverse packets list to get the order right*)
  pcap_contents <-
    { pcap_contents
      with packets = List.rev pcap_contents.packets }
  fd.Close ()
  pcap_contents
