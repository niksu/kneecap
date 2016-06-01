Kneecap enables you to generates pcap files from a high-level logical spec.
More details at the <a href="http://www.cl.cam.ac.uk/~ns441/kneecap/">website.</a>

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
xbuild Microsoft.Z3.csproj
```
3) We will use Z3 to build Kneecap. Copy files over.
```
cp ${Z3_DIR}/src/api/dotnet/obj/Debug/Microsoft.Z3.dll ${KNEECAP_DIR}/kneecap
cp ${Z3_DIR}/build/libz3* ${KNEECAP_DIR}/kneecap
```
4) Build Kneecap
```
cd ${KNEECAP_DIR}
./build.sh
```

## Running
`$ MONO_PATH=${MONO_PATH}:${KNEECAP_DIR}/kneecap/ mono ${KNEECAP_DIR}/kneet/kneet.exe`
You should see a list of numbers counting up to a thousand, at the end of which
the program will terminate. Each of the numbers corresponded to a packet being
generated, which was recorded in a .pcap file in your directory.

## Problems?
Mono might complain that it cannot find certain files. Sometimes such error messages
can be misleading: Mono *can* find the files, but they don't contain what it
expected to find. Set `MONO_LOG_LEVEL=debug` in your environment to have Mono
tell you more.
