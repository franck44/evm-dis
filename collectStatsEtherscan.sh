

# Generate a directory of contracts from a list of addresses in a file.
echo "Collecting stats Etherscan for contract address in file: " $1

echo "" >etherscan/stats.txt
# create the etherscan dir if it doesn't exist
# mkdir -p etherscan 
while read line; do # 'line' is the variable name
    # mkdir -p etherscan/$line
    # curl -L -s https://api.etherscan.io/api\?module\=proxy\&action\=eth_getCode\&address\="$line"\&apikey\="$key" > tmp.txt
    # cat tmp.txt | sed  's/\,/\n/g' | sed 's/:/\n/g' | grep 0x | sed 's/\"//g' | sed 's/}//g' > etherscan/$line/bytecode_$line.evm 
    # \rm -Rf tmp.txt
    # ./makeCFG.sh etherscan/$line/bytecode_$line.evm
    maxD=`cat etherscan/$line/bytecode_$line-cfg.dot | grep "maxDepth is" | sed 's/maxDepth is://g'`
    # echo "maxDepth is $maxD"
    maxReached=`cat etherscan/$line/bytecode_$line-cfg.dot | grep "MaxDepth reached:" | sed 's/MaxDepth reached://g'`
    # echo "maxDepthReached is $maxReached"
    errors=`cat etherscan/$line/bytecode_$line-cfg.dot | grep "ErrorStates reached:" | sed 's/ErrorStates reached://g'`
    # echo "errors is $errors"
    nodesRaw=`cat etherscan/$line/bytecode_$line-cfg.dot | grep "Size of non minimised CFG:" | sed 's/Size of non minimised CFG://g' | sed 's/\,/\n/' | grep "nodes" | sed 's/nodes//g'`
    # echo "nodesRaw is $nodesRaw"
    edgesRaw=`cat etherscan/$line/bytecode_$line-cfg.dot | grep "Size of non minimised CFG:" | sed 's/Size of non minimised CFG://g' | sed 's/\,/\n/' | grep "edges" | sed 's/edges//g'`
    # echo "edgesRaw is $edgesRaw"
    nodesMin=`cat etherscan/$line/bytecode_$line-cfg.dot | grep "Size of minimised CFG:" | sed 's/Size of minimised CFG://g' | sed 's/\,/\n/' | grep "nodes" | sed 's/nodes//g'`
    # echo "nodesMin is $nodesMin"
    edgesMin=`cat etherscan/$line/bytecode_$line-cfg.dot | grep "Size of minimised CFG:" | sed 's/Size of minimised CFG://g' | sed 's/\,/\n/' | grep "edges" | sed 's/edges//g'`
    # echo "edgesMin is $edgesMin"
    # check if it has unsuppoprted instructions RJUMPs 
    rjumps=`./disassemble.sh etherscan/$line/bytecode_$line.evm | grep "RJUMP" | wc -l | sed 's/ //g'`
    # add entry to stats file 
    echo "$line,$maxD,$maxReached,ERRORS=0$errors,$nodesRaw,$edgesRaw,$nodesMin,$edgesMin,RJUMPS=$rjumps" >> etherscan/stats.txt
done <$1
