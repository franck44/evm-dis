#!/bin/bash

# usage ./makeProofObj.sh <filename> <segment size>?
echo "Processing file: " $1

filename=$1
shortname=$(basename -- "$filename")
shortname="${shortname%.*}"
extension="${filename##*.}"
filename="${filename%.*}"
segsize="20" 

# output file, dafny code
output="build/proofs/$shortname/$shortname-cfg-verifier.dfy"
# create the target dir if it does not exist 
mkdir -p build/proofs/$shortname

# output file location
echo "Shortname: " $shortname "// resulting file: " $output

# if no segment size provided use default 10
if [ "$#" -eq 2 ]; then
    segsize=$2
fi
echo "seg size: $segsize"

# run evmdis to generate the dafny code
java -jar build/libs/Driver-java/evmdis.jar --title $shortname -p  --size $segsize --cfg 100 --raw $(<$1) >$output

# format the code
dafny format  $output
# do not verify with dafny 
# dafny verify --allow-warnings --verification-time-limit 200  $output



