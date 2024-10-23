#!/bin/bash

# usage ./verifyEtherscan.sh <filename> segsize <resultfile>
resultfile=$3
echo "% Segsize is $2" >$resultfile

mkdir -p build/proofs/etherscan/

while read line; do # 'line' is the variable name
    filename=${line:0:42}
    # shortname=$(basename -- "$filename")
    # extension="${filename##*.}"
    # filename="${filename%.*}"
    mkdir -p build/proofs/etherscan/$filename
   java -jar build/libs/Driver-java/evmdis.jar --title $shortname -p  --size $2 --cfg 100 --raw --lib ../../../../../evm-dafny $(<etherscan/$filename/bytecode_$filename.evm) >build/proofs/etherscan/$filename/$filename-cfg-verifier.dfy
    sed -i '' -e 's/include\ \"/include\ \"..\//g' build/proofs/etherscan/$filename/$filename-cfg-verifier.dfy
    dafny format build/proofs/etherscan/$filename/$filename-cfg-verifier.dfy
    dafny verify --cores=12 build/proofs/etherscan/$filename/$filename-cfg-verifier.dfy
    if [ $? -eq 0 ] 
    then 
        echo "Success" 
        echo $filename " verified: true"  >>$resultfile
    else 
        echo "Failure" 
        echo $filename " verified: false"  >>$resultfile
    fi
done <$1

