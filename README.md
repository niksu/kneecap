Kneecap enables you to generates pcap files from a high-level logical spec.
More details at the <a href="http://www.cl.cam.ac.uk/~ns441/kneecap/">website.</a>

## Dependencies
* Z3 (version 4.x). Download the source from <a href="https://github.com/Z3Prover/z3/releases">Z3's release archive</a>.
* Mono runtime and F# compiler.

## Building
I ran this on Ubuntu 14, but the process should be similar on other systems.

Let `$KNEECAP_DIR` be the path of your Kneecap clone.
1. Get a Z3 release from https://github.com/Z3Prover/z3/releases and build it.
```
# go to directory where you've untarred Z3.
export Z3_DIR=`pwd`
./configure
cd build; make
```
2. Build the managed wrapper to Z3.
```
cd ../src/api/dotnet
xbuild Microsoft.Z3.csproj
```
3. We will use Z3 to build Kneecap. Copy files over.
```
cp ${Z3_DIR}/src/api/dotnet/obj/Debug/Microsoft.Z3.dll ${KNEECAP_DIR}/kneecap
cp ${Z3_DIR}/build/libz3* ${KNEECAP_DIR}/kneecap
```
4. Build Kneecap
```
cd ${KNEECAP_DIR}
./build.sh
```

## Running
MONO_PATH=${MONO_PATH}:${KNEECAP_DIR}/kneecap/ mono ${KNEECAP_DIR}/kneet/kneet.exe
