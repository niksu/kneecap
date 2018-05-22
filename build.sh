#!/bin/sh

cd kneecap
rm kneecap.dll
make
cd ../kneet
rm kneet.exe
make
cd ..
