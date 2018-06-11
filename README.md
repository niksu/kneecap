![Kneecap](doc/small_kneecap.jpg)

Kneecap enables you to generate network packets from a high-level logical spec such as this [example](https://github.com/niksu/kneecap/blob/master/kneet/Program.fs#L35):
```fsharp
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
```
This example describes an IPv4 packet encapsulated inside an Ethernet frame, and specifies constraints on both layers.
This spec is translated into bitvector constraints that are given to an SMT solver.
Solutions returned by the solver correspond to network packets.
You can find out more by reading the [paper](https://www.nik.network/cucl/files/kneecap_smt16.pdf).

## Example output
Kneecap provides an API for generating packets. It comes with a [sample program](https://github.com/niksu/kneecap/blob/master/kneet/Program.fs) that
generates packets using Kneecap and then saves them in the
[pcap](https://en.wikipedia.org/wiki/Pcap) [file format](https://wiki.wireshark.org/Development/LibpcapFileFormat).
You can view these files' contents using tools like [Wireshark](https://www.wireshark.org/)
or various [others](http://serverfault.com/questions/38626/how-can-i-read-pcap-files-in-a-friendly-format).
This section contains example output files from this sample program.

### 64-byte Ethernet packets, in batches of 1000
* [ethernet_64_1.pcap](https://www.nik.network/kneecap/ethernet_64_1.pcap)
* [ethernet_64_2.pcap](https://www.nik.network/kneecap/ethernet_64_2.pcap)
* [ethernet_64_3.pcap](https://www.nik.network/kneecap/ethernet_64_3.pcap)
* [ethernet_64_4.pcap](https://www.nik.network/kneecap/ethernet_64_4.pcap)

### 584-byte Ethernet packets, in batches of 1000
* [ethernet_584_1.pcap](https://www.nik.network/kneecap/ethernet_584_1.pcap)
* [ethernet_584_2.pcap](https://www.nik.network/kneecap/ethernet_584_2.pcap)
* [ethernet_584_3.pcap](https://www.nik.network/kneecap/ethernet_584_3.pcap)
* [ethernet_584_4.pcap](https://www.nik.network/kneecap/ethernet_584_4.pcap)

### 1000 packets containing six stacked protocols, described in the paper
* [stack_6_1000.pcap](https://www.nik.network/kneecap/stack_6_1000.pcap)

## Dependencies
* Z3 (version 4.x). Download the source from <a href="https://github.com/Z3Prover/z3/releases">Z3's release archive</a>.
* Mono runtime and F# compiler.

## Building
I ran this on Ubuntu 14 (using Mono 3.2.8) and OSX 10.10.5 (using Mono 3.8.0), but the process should be similar on other systems.

Let `$KNEECAP_DIR` be the path of your Kneecap repo clone.

1) Get a Z3 release from https://github.com/Z3Prover/z3/releases and build it.
```
# go to directory where you've untarred Z3.
export Z3_DIR=`pwd`
./configure
cd build; make
```
> **Note**: On OSX I gave the `--x86` command-line flag to `./configure`, since
> for some reason the version of Mono I'm using expected Z3's DLL to be compiled
> for 32.bit

2) Build the managed wrapper to Z3.
```
cd ../src/api/dotnet
msbuild Microsoft.Z3.csproj
```
3) We will use Z3 to build Kneecap. Copy files over.
```
cp ${Z3_DIR}/src/api/dotnet/obj/Debug/Microsoft.Z3.dll ${KNEECAP_DIR}
```
4) Build Kneecap
```
cd ${KNEECAP_DIR}
msbuild kneecap.sln
```

## Running
`$ MONO_PATH=${MONO_PATH}:${KNEECAP_DIR}/kneecap/ mono ${KNEECAP_DIR}/kneet/bin/Debug/kneet.exe`

You should see a list of numbers counting up to a thousand, at the end of which
the program will terminate. Each of the numbers corresponded to a packet being
generated, which was recorded in a .pcap file in your directory.

## Problems?
Mono might complain that it cannot find certain files. Sometimes such error messages
can be misleading: Mono *can* find the files, but they don't contain what it
expected to find. Set `MONO_LOG_LEVEL=debug` in your environment to have Mono
tell you more.
