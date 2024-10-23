#!/bin/bash

#usage ./collectStatsEtherscan.sh <directory> <output file>
# Generate stats for computed CFGs
echo "Collecting stats for CFGs in " $1

basedir=$1
resfile=$2 

echo "" >$resfile

# while read line; do # 'line' is the variable name
for file in "$basedir"/*.dot; do
    line=$(basename -- "$file")
    # echo "Processing line: " $line
    input=$basedir/$line
    # echo "Processing file: " $input
    maxD=`cat $input | grep "maxDepth is" | sed 's/maxDepth is://g'`
    # echo "maxDepth is $maxD"
    maxReached=`cat $input | grep "MaxDepth reached:" | sed 's/MaxDepth reached://g'`
    # echo "maxDepthReached is $maxReached"
    errors=`cat $input | grep "ErrorStates reached:" | sed 's/ErrorStates reached://g'`
    # echo "errors is $errors"
    nodesRaw=`cat $input | grep "Size of non minimised CFG:" | sed 's/Size of non minimised CFG://g' | sed 's/\,/\n/' | grep "nodes" | sed 's/nodes//g'`
    # echo "nodesRaw is $nodesRaw"
    edgesRaw=`cat $input | grep "Size of non minimised CFG:" | sed 's/Size of non minimised CFG://g' | sed 's/\,/\n/' | grep "edges" | sed 's/edges//g'`
    # echo "edgesRaw is $edgesRaw"
    nodesMin=`cat $input | grep "Size of minimised CFG:" | sed 's/Size of minimised CFG://g' | sed 's/\,/\n/' | grep "nodes" | sed 's/nodes//g'`
    # echo "nodesMin is $nodesMin"
    edgesMin=`cat $input | grep "Size of minimised CFG:" | sed 's/Size of minimised CFG://g' | sed 's/\,/\n/' | grep "edges" | sed 's/edges//g'`
    # echo "edgesMin is $edgesMin"
    # check if it has unsuppoprted instructions RJUMPs 
    # rjumps=`./disassemble.sh $input | grep "RJUMP" | wc -l | sed 's/ //g'`
    # add entry to stats file 
    echo "$line,$maxD,$maxReached,ERRORS=0$errors,$nodesRaw,$edgesRaw,$nodesMin,$edgesMin" >>$resfile
done <$1
