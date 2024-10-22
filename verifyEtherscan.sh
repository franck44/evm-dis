
resultfile="etherscan/verification-stats-batch5.txt"
echo "" >$resultfile

while read line; do # 'line' is the variable name
    filename=$line
    shortname=$(basename -- "$filename")
    extension="${filename##*.}"
    filename="${filename%.*}"
   java -jar build/libs/Driver-java/evmdis.jar --title $shortname -p  --size 1 --cfg 100 --raw --lib ../../../../../evm-dafny $(<etherscan/$line/bytecode_$line.evm) >etherscan/$line/$line-cfg-verifier.dfy
    dafny format etherscan/$line/$line-cfg-verifier.dfy
    dafny verify --cores=12 etherscan/$line/$line-cfg-verifier.dfy
    if [ $? -eq 0 ] 
    then 
        echo "Success" 
        echo $line " verified: true"  >>$resultfile
    else 
        echo "Failure" 
        echo $line " verified: false"  >>$resultfile
    fi
    # dafny /dafnyVerify:1 /compile:0 /traceTimes /tracePOs --format csv $filename-cfg-verifier.dfy
    # status=$(grep "Dafny program verifier finished with" verif-res.tmp)
    # echo "Verified processing contract address: " $line " status" $status >>etherscan/verification-stats.txt
done <$1

