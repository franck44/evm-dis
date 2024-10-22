#!/bin/sh

echo "Processing file: " $1

filename=$1
shortname=$(basename -- "$filename")
extension="${filename##*.}"
filename="${filename%.*}"
segsize="10" 

echo "Shortname: " $shortname
if [ "$#" -eq 2 ]; then
    segsize=$2
fi
echo "seg size: $segsize"

java -jar build/libs/Driver-java/evmdis.jar --title $shortname -p  --size $segsize --cfg 100 --raw --lib ../../../../../evm-dafny $(<$1) >$filename-cfg-verifier.dfy
dafny format  $filename-cfg-verifier.dfy
dafny verify --allow-warnings $filename-cfg-verifier.dfy


