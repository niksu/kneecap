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

module kneecap


(*
stratified constraint solving/checking -- following protocol layer

breaking up deterministic computations, backtracking, and "learning" non-viable paths, to avoid them in the future

controlling the backend solver
*)

let generate_packets (generator : packets.packet) (quantity : uint32) (f : packets.packet -> bool) : (uint32 * byte[]) list =
  general.enumerate (int quantity - 1)
  |> List.fold (fun (active, st) i ->
         if not active || not (generator.generate ()) then
           (false, st)
         else
           match generator.extract_packet () with
           | None -> failwith "Could not extract the generated packet"
           | Some bytes ->
               if not (f generator) then
                 generator.solution <- None
                 (false, st)
               else
                 (true, (uint32 i, bytes) :: st))
     (true, [])
  |> snd
  |> List.rev (*preserve order*)

(*NOTE i assume that the generator has already been constrained*)
let generate_pcap_contents (generator : packets.packet) (quantity : uint32) (f : packets.packet -> bool) : pcap.pcap_file_contents =
(*FIXME give raw packets as a parameter to generator, together with metadata (per-packet pcap header)*)
  let raw_packets = generate_packets generator quantity f
  assert (List.length raw_packets = int quantity)
  assert (generator.packet_size <= pcap.default_global_header.snaplen)
  {global_header = pcap.default_global_header;
   packets = List.map (fun (i, pckt) ->
     { header =
         { ts_sec = i;
           ts_usec = 0u;
           incl_len = uint32 (Array.length pckt);
           orig_len = uint32 (Array.length pckt);
         };
       data = pckt
     }) raw_packets
    }

let generate_timed_pcap_contents (generator : packets.packet) (quantity : uint32) (f : packets.packet -> bool) : pcap.pcap_file_contents =
  assert (generator.packet_size <= pcap.default_global_header.snaplen)

  use countdown = new System.Timers.Timer(30000.)
  countdown.AutoReset <- true
  countdown.Elapsed.Add (fun _ ->
    printfn "GC'd\n"
    System.GC.Collect ())
  //countdown.Start ()
  let timer = System.Diagnostics.Stopwatch.StartNew ()
  let sw = System.Diagnostics.Stopwatch.StartNew ()
  let result =
    {pcap.global_header = pcap.default_global_header;
     pcap.packets = List.fold (fun acc i ->
       let pckt : byte [] option =
         if not (generator.generate ()) then
           printf "%d : Could not generate\n" i
           None
         else
           match generator.extract_packet () with
           | None ->
             failwith "Could not extract the generated packet"
           | Some bytes ->
               ignore(f generator)
               Some bytes
       match pckt with
       | None -> acc
       | Some actual_pckt ->
         let t = timer.ElapsedMilliseconds
         printf "%d : %d\n" i t
         timer.Restart()
         { header =
             { ts_sec = 0u;
               ts_usec = uint32 t; (*FIXME precision loss*)
               incl_len = uint32 (Array.length actual_pckt);
               orig_len = uint32 (Array.length actual_pckt);
             };
           data = actual_pckt
         } :: acc) [] (general.enumerate (int quantity - 1))
      }
  printfn "Finished: %d ms\n" sw.ElapsedMilliseconds
  countdown.Stop ()
  timer.Stop()
  sw.Stop()
  result
