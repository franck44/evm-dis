#!/bin/sh

echo "Processing file: " $1

filename=$1
shortname=$(basename -- "$filename")
extension="${filename##*.}"
filename="${filename%.*}"

echo "Shortname: " $shortname
java -jar build/libs/Driver-java/evmdis.jar --title $shortname --cfg 100 $(<$1) >$filename-cfg.dot
dot -Tsvg $filename-cfg.dot -o $filename-cfg.svg

