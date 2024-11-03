#!/bin/bash

# usage ./makeCFGEtherscan.sh <filename> 

filename=$1
shortname=$(basename -- "$filename")
shortname="${shortname%.*}"

resultfile="etherscan/verification-results-for-$shortname.txt"

n=$(wc -l $1)
echo "Files to process: $n" 

echo "" >$resultfile

mkdir -p build/etherscan/cfgs

count=0
while read line; do # 'line' is the variable name
   count=$((count+1))
   output=${line:0:42}
   echo "[$count/$n] Processing contract address:|$output|"
   java -jar build/libs/Driver-java/evmdis.jar --title $shortname --cfg 100 $(<etherscan/$output/bytecode_$output.evm) >build/etherscan/cfgs/$output-cfg.dot
   echo "CFG (DOT) file created in: " build/etherscan/cfgs/$output-cfg.dot
done <$1

