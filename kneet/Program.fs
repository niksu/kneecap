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

open general
open packets
open ethernet
open etherip
open ipv4
open arp
open kneecap

[<EntryPoint>]
let main argv = 
    printfn "Creating scheme."
    use eth = new ethernet(184u)
    printfn "ethernet packet size in bits: %d" eth.packet_size

    use ip = new ipv4(180u)
    printfn "ipv4 packet size in bits: %d" ip.packet_size

    printfn "Adding constraints."
    eth.constrain <@ ethernet.source_address = ethernet.mac_address "[1-5,10]:34:56:78:90:*" &&
                     ethernet.ethertype = ethernet.ethertype_ipv4 @>
    <== ip.constrain <@@ ipv4.version = 4 &&
                         ipv4.source_address = ipv4.ipv4_address "10.10.10.[55-60]" &&
                         ipv4.source_address = ipv4.destination_address &&
                         ipv4.internet_header_length = 5 &&
                         ipv4.total_length = 170 &&
                         ipv4.TTL = 5 &&
                         ipv4.protocol = ipv4.protocol_ip_in_ip
                         (*ipv4.source_address < ipv4.destination_address*)
                      @@>

    ip +==
      [(new ipv4(150u)).constrain
        <@ ipv4.version = 4 &&
           ipv4.source_address = ipv4.ipv4_address "192.168.4.[55-60]" &&
           ipv4.destination_address = ipv4.ipv4_address "194.100.[1-254].[10-20]" &&
           ipv4.internet_header_length = 5 &&
           ipv4.total_length = 150 &&
           ipv4.TTL = 7 &&
           ipv4.protocol = ipv4.protocol_etherip
         @>;

       (new etherip(100u)).constrain <@ etherip.version = 3 @>;

       (new ethernet(80u)).constrain
        <@ ethernet.source_address = ethernet.mac_address "00:11:22:33:44:55" &&
           ethernet.destination_address = ethernet.mac_address "13:24:35:46:57:68" &&
           ethernet.ethertype = ethernet.ethertype_arp @>;

       (new arp<ethernet, ipv4>(eth, ip)).constrain
        <@ arp<ethernet, ipv4>.HTYPE = arp<ethernet, ipv4>.HTYPE_ethernet &&
           arp<ethernet, ipv4>.PTYPE = arp<ethernet, ipv4>.PTYPE_ipv4 &&
           arp<ethernet, ipv4>.HLEN = 6 &&
           arp<ethernet, ipv4>.PLEN = 4 &&
           arp<ethernet, ipv4>.OPER = arp<ethernet, ipv4>.OPER_Reply
         @>]

    printfn "Added constraints. Generating packets next."
    let x = eth.assertion ()
    let x = ip.assertion ()

    generate_timed_pcap_contents eth 1000u (fun (p : packet) -> ignore(p.constrain_different()))
    |> pcap.serialise_pcap @"X:\stack_6_1000.pcap"

    printfn "%A" argv
    0 // return an integer exit code
