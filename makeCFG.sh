#!/bin/bash

# usage ./makeCFG.sh <filename> <segment size>?
echo "Processing file: " $1

filename=$1
shortname=$(basename -- "$filename")
extension="${filename##*.}"
filename="${filename%.*}"

# output file, dafny code
output="build/dot/$shortname/$shortname.dot"
# create the target dir if it does not exist 
mkdir -p build/dot/$shortname

depthsize="100" 
# if no max size provided use default 100
if [ "$#" -eq 2 ]; then
    depthsize=$2
fi
echo "Max depth size: $depthsize"

echo "Shortname: " $shortname
java -jar build/libs/Driver-java/evmdis.jar --title $shortname --cfg $depthsize $(<$1) >$output
#dot -Tsvg $filename-cfg.dot -o $filename-cfg.svg

