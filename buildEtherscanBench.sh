#!/bin/bash

key="${ETHERSCAN_API_KEY}"

# Generate a directory of contracts from a list of addresses in a file.
echo "Collecting bytecodes from Etherscan for contract address in file: " $1

# create the etherscan dir if it doesn't exist
mkdir -p etherscan 
while read line; do # 'line' is the variable name
    mkdir -p etherscan/$line
    curl -L -s https://api.etherscan.io/api\?module\=proxy\&action\=eth_getCode\&address\="$line"\&apikey\="$key" > tmp.txt
    cat tmp.txt | sed  's/\,/\n/g' | sed 's/:/\n/g' | grep 0x | sed 's/\"//g' | sed 's/}//g' > etherscan/$line/bytecode_$line.evm 
    \rm -Rf tmp.txt
    ./makeCFG.sh etherscan/$line/bytecode_$line.evm
    #    echo "out" >etherscan/$line # do something here
done <$1
