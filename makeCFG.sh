#!/bin/bash

# usage ./makeCFG.sh <filename> <depth>?
echo "Processing file: " $1

filename=$1
shortname=$(basename -- "$filename")
extension="${filename##*.}"
filename="${filename%.*}"

# output file, dafny code
shortnamenoext="${shortname%.*}"
echo $shortnamenoext
output="build/dot/$shortnamenoext/$shortnamenoext.dot"
# create the target dir if it does not exist 
mkdir -p build/dot/$shortnamenoext

depthsize="100" 
# if no max depth provided use default 100
if [ "$#" -eq 2 ]; then
    depthsize=$2
fi
echo "Max depth size: $depthsize"
echo "Shortname: " $shortname
java -jar build/libs/Driver-java/evmdis.jar --title $shortnamenoext --cfg $depthsize $(<$1) >$output
echo "CFG (DOT) format generared in $output"


