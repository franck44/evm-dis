#!/bin/sh

echo "Processing file: " $1

filename=$1
shortname=$(basename -- "$filename")
extension="${filename##*.}"
filename="${filename%.*}"

echo "Shortname: " $shortname
java -jar build/libs/Driver-java/evmdis.jar --title $shortname -e  --cfg 100 --raw --lib ../../../../../../evm-dafny $(<$1) >$filename-proofObj.dfy
echo "Generated: " $filename-proofObj.dfy
# dafny format $filename-proof.dfy

