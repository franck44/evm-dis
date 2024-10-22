#!/bin/sh

echo "Processing file: " $1

filename=$1
shortname=$(basename -- "$filename")
extension="${filename##*.}"
filename="${filename%.*}"

echo "Shortname: " $shortname
java -jar build/libs/Driver-java/evmdis.jar --title $shortname -p  --size 10 --cfg 100 --raw --lib ../../../../../evm-dafny $(<$1) >$filename-cfg-verifier.dfy
# dafny format $filename-verifier.dfy
dafny /dafnyVerify:1 /compile:0 /traceTimes /tracePOs $filename-cfg-verifier.dfy

