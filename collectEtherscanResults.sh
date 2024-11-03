#!/bin/bash

# usage ./collectEtherscanResults.sh <filename> 

mkdir -p build/proofs/etherscan/

while read line; do # 'line' is the variable name
    filename=${line:0:42}
    errors=$(cat build/proofs/etherscan/$filename/$filename-cfg-verification-stats.csv | grep Failed | wc -l) 
    echo "build/proofs/etherscan/$filename/$filename-cfg-verifier.dfy: errors: $errors"
    if [ $errors -eq "0" ] 
    then 
        echo "$filename: Success" 
    else 
        echo "$filename: $errors Failure(s)" 
    fi
done <$1

