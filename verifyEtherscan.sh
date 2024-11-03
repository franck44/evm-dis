#!/bin/bash

# assumes the dfy file has already been generated with makeProofObjEtherscan.sh 

# usage ./verifyEtherscan.sh <filename> 

mkdir -p build/proofs/etherscan/

while read line; do # 'line' is the variable name
    filename=${line:0:42}
    mkdir -p build/proofs/etherscan/$filename
    echo "processing $filename" 
    dafny verify --cores=12 --error-limit 1 --verification-time-limit 200 --log-format "csv;LogFileName=build/proofs/etherscan/$filename/$filename-cfg-verification-stats.csv"   build/proofs/etherscan/$filename/$filename-cfg-verifier.dfy
    if [ $? -eq 0 ] 
    then 
        echo "Success" 
    else 
        echo "Failure" 
    fi
done <$1

