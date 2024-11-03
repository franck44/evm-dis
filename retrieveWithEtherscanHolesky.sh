#!/bin/bash
# pull a contract bytecode form ethereum
# address is first param 
echo "Fetching bytecode from Etherscan for contract address: " $1

# You need an API key to perform this operation 
key="${ETHERSCAN_API_KEY}"
echo "Your API key is $key"
curl -L -s https://api-holesky.etherscan.io/api\?module\=proxy\&action\=eth_getCode\&address\="$1"\&apikey\="$key" > tmp.txt
cat tmp.txt | sed  's/\,/\n/g' | sed 's/:/\n/g' | grep 0x | sed 's/\"//g' | sed 's/}//g' > etherscan_holesky_$1.evm 
echo "Bytecode for $1 saved to file: " etherscan_holesky_$1.evm
\rm -Rf tmp.txt
