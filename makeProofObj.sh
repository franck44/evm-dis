#!/bin/sh

echo "Processing file: " $1

filename=$1
shortname=$(basename -- "$filename")
extension="${filename##*.}"
filename="${filename%.*}"

echo "Shortname: " $shortname
java -jar build/libs/Driver-java/evmdis.jar --title $shortname -p  --cfg 100 --raw --lib ../../../../../evm-dafny $(<$1) >$filename-proof.dfy
# dafny format $filename-proof.dfy

