#!/bin/sh
# address is first param 
echo "Fetching bytecode from Etherscan for contract address: " $1

key="${ETHERSCAN_API_KEY}"
echo "Your API key is $key"
curl -L -s https://api.etherscan.io/api\?module\=proxy\&action\=eth_getCode\&address\="$1"\&apikey\="$key" > tmp.txt
cat tmp.txt | sed  's/\,/\n/g' | sed 's/:/\n/g' | grep 0x | sed 's/\"//g' | sed 's/}//g' > etherscan_$1.evm 
\rm -Rf tmp.txt

# filename=$1
# shortname=$(basename -- "$filename")
# extension="${filename##*.}"
# filename="${filename%.*}"

# echo "Shortname: " $shortname
# java -jar build/libs/Driver-java/evmdis.jar --title $shortname --cfg 100 $(<$1) >$filename-cfg.dot
# dot -Tsvg $filename-cfg.dot -o $filename-cfg.svg

