
This page describes how to use the [docker](https://www.docker.com) image to reproduce some experimental results.

# Overview

The Docker image is available at [evm-dis-docker-image]().
To use it you need a working version of  [docker](https://www.docker.com).
You can install Docker on your system following these [steps](https://docs.docker.com/engine/install/).

To check that docker is properly installed, you may run

```zsh
evm-dis git:(main) ✗ docker --version
Docker version 27.2.0, build 3ab4256
```

# Using the Docker image

The Docker image contains a working version of Dafny (4.8.1), Java (23.0.1), Python3.
You can download the image with (this can take while to download ...):

```zsh
docker image pull franck44/tacas25:latest --platform linux/amd64
```

The image also contains some examples of bytecode in the `src/dafny/test/src` folder.

You can now start a Docker container with the image  with the command:

```zsh
evm-dis git:(main) ✗ docker run -it franck44/tacas25
root@70bf3cda14c9:/# cd tacas25/evm-dis
root@70bf3cda14c9:/tacas25/evm-dis# java -version
java version "23.0.1" 2024-10-15
Java(TM) SE Runtime Environment (build 23.0.1+11-39)
Java HotSpot(TM) 64-Bit Server VM (build 23.0.1+11-39, mixed mode, sharing)
root@70bf3cda14c9:/tacas25/evm-dis# dafny --version
4.8.1+d15eef77080d3262d783bbed92b285bf148cce6b
root@70bf3cda14c9:/tacas25/evm-dis# python3 --version
Python 3.12.3
```

## Disassembler

You can use the disassembler

```zsh
root@70bf3cda14c9:/tacas25/evm-dis# ./disassemble.sh src/dafny/tests/src/simple/simpleCall.bin 
Processing file:  src/dafny/tests/src/simple/simpleCall.bin
Shortname:  simpleCall.bin
Disassembled code:
00000000: PUSH1 0x07
00000002: PUSH1 0x08
00000004: PUSH1 0x10
00000006: JUMP
00000007: JUMPDEST
00000008: PUSH1 0x40
0000000a: MSTORE
0000000b: PUSH1 0x20
0000000d: PUSH1 0x40
0000000f: RETURN
00000010: JUMPDEST
00000011: SWAP1
00000012: JUMP
--------------- Disassembled ---------------------
```

## Building a CFG

You can generate a CFG (DOT format) for the binary the command:

```zsh
root@70bf3cda14c9:/tacas25/evm-dis# ./makeCFG.sh src/dafny/tests/src/simple/simpleCall.bin 
Processing file:  src/dafny/tests/src/simple/simpleCall.bin
simpleCall
Max depth size: 100
Shortname:  simpleCall.bin
CFG (DOT) format generared in build/dot/simpleCall/simpleCall.dot
root@70bf3cda14c9:/tacas25/evm-dis#  more build/dot/simpleCall.bin/simpleCall.bin.dot 
/*
maxDepth is:100
MaxDepth reached:false
ErrorStates reached:0
States seen:0
WPre success:0
# of reachable invalid segments is: 0
Size of non minimised CFG: 3 nodes, 2 edges
Size of minimised CFG: 3 nodes, 2 edges
Minimised CFG
*/
// Number of states: 3
// Number of transitions : 2
...
```

The result file, `simpleCall.bin.dot`, is in the folder `build/dot/simpleCall.bin`.

## Verification of the CFG

The CFG for `simpleCall.bin` can be verified by generating a Dafny program and verifying it as follows:

```zsh
root@70bf3cda14c9:/tacas25/evm-dis# ./verifyCFG.sh src/dafny/tests/src/simple/simpleCall.bin 
Processing file:  src/dafny/tests/src/simple/simpleCall.bin
Shortname:  simpleCall // resulting file:  build/proofs/simpleCall/simpleCall-cfg-verifier.dfy
seg size: 20

Dafny program verifier finished with 3 verified, 0 errors
root@70bf3cda14c9:/tacas25/evm-dis# 
```

The Dafny source code is in `build/proofs/simpleCall/simpleCall-cfg-verifier.dfy`:

```zsh
root@70bf3cda14c9:/tacas25/evm-dis# more build/proofs/simpleCall/simpleCall-cfg-verifier.dfy  
include "../../../src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module  {:disableNonlinearArithmetic} EVMProofObject {

  import opened AbstractSemantics
  import opened AbstractState

  /** Node 0
    * Segment Id for this node is: 0
    * Starting at 0x0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s0(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x07);
      assert s1.Peek(0) == 0x7;
      var s2 := Push1(s1, 0x08);
      var s3 := Push1(s2, 0x10);
      assert s3.Peek(0) == 0x10;
      assert s3.Peek(2) == 0x7;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ...
```

## Persisting CFG (DOT) files

To retrieve the CFG (DOT format) on your host machine you run the image as follows:

```zsh
docker run -v /tmp:/tmp -it tacas25 
root@09b31c7a9d50:/# cd tacas25/evm-dis
root@09b31c7a9d50:/tacas25/evm-dis# ./makeCFG.sh src/dafny/tests/src/simple/simpleCall.bin 
Processing file:  src/dafny/tests/src/simple/simpleCall.bin
Max depth size: 100
Shortname:  simpleCall.bin
root@09b31c7a9d50:/tacas25/evm-dis# cp build/dot/simpleCall.bin/simpleCall.bin.dot /tmp
root@09b31c7a9d50:/tacas25/evm-dis#
```

The DOT file `simpleCall.bin.dot` will be available on your **host** `/tmp` folder.

you can use the [Graphviz-Online](https://dreampuf.github.io/GraphvizOnline/) tool to visualise the `dot` files.

## Generating and Verifying the Etherscamn benchmarks
The generation and verification of the 978 Etherscan benchmarks is done with the following commands:
(arguments are the input file, the maximum segment size, and the output result file):
```zsh 
root@09b31c7a9d50:/# ./makeProofObjEtherscan.sh etherscan/success_files_1_100.txt 40 result_generation_files_1_100.txt 
0xe99fcd9396dbc294055350267b8257e9b05f01ac: Success
0xfcd5b675ae8e9dd0172c84568b6ef504e1dc8619: Success
0xa24d3886be3557782eeffb5f6ac6a4bb24faff55: Success
0x5d5bb5bdb7a228fd2f0f90c5ec7e5bc609529821: Success
0x1a0205cd3fa5b3d8a11444a14b6c0fc993c2dc14: Success
...
```

The result file will indicate for each benchmark whether the generation of the proof objeft was successful or not.

```zsh
root@09b31c7a9d50:/# more result_generation_files_1_100.txt 
% Segsize is 40
0xe99fcd9396dbc294055350267b8257e9b05f01ac  proof object generated: true
0xfcd5b675ae8e9dd0172c84568b6ef504e1dc8619  proof object generated: true
0xa24d3886be3557782eeffb5f6ac6a4bb24faff55  proof object generated: true
0x5d5bb5bdb7a228fd2f0f90c5ec7e5bc609529821  proof object generated: true
0x1a0205cd3fa5b3d8a11444a14b6c0fc993c2dc14  proof object generated: true
0xDcfCcaf54CB8c7c30bb7959929AbA24bF136FF57  proof object generated: true
0x5b348ec54c290683697f6a812ca1bfbb0e74c70d  proof object generated: true
0x9a1ba1687c2759fe96bfacbfb5300458b7d726f0  proof object generated: true
... 
```

The benchmarks are verified with the following command:
```zsh
root@09b31c7a9d50:/# ./verifyEtherscan.sh etherscan/success_files_1_100.txt 
processing 0xe99fcd9396dbc294055350267b8257e9b05f01ac
Dafny program verifier finished with 224 verified, 0 errors
Results File: /Users/franck/development/evm-dis/build/proofs/etherscan/0xe99fcd9396dbc294055350267b8257e9b05f01ac/0xe99fcd9396dbc294055350267b8257e9b05f01ac-cfg-verification-stats.csv
Success
...
``` 
The verificaiton result (csv) file contains the verification status for each node in the CFG.


To collect the results of the verification for a set of benchmarks, you can use the following command:
```zsh
root@09b31c7a9d50:/# ./collectEtherscanResults.sh etherscan/success_files_1_100.txt
build/proofs/etherscan/0xe99fcd9396dbc294055350267b8257e9b05f01ac/0xe99fcd9396dbc294055350267b8257e9b05f01ac-cfg-verifier.dfy: errors:        0
0xe99fcd9396dbc294055350267b8257e9b05f01ac: Success
build/proofs/etherscan/0xfcd5b675ae8e9dd0172c84568b6ef504e1dc8619/0xfcd5b675ae8e9dd0172c84568b6ef504e1dc8619-cfg-verifier.dfy: errors:        0
0xfcd5b675ae8e9dd0172c84568b6ef504e1dc8619: Success
build/proofs/etherscan/0xa24d3886be3557782eeffb5f6ac6a4bb24faff55/0xa24d3886be3557782eeffb5f6ac6a4bb24faff55-cfg-verifier.dfy: errors:        0
0xa24d3886be3557782eeffb5f6ac6a4bb24faff55: Success
build/proofs/etherscan/0x5d5bb5bdb7a228fd2f0f90c5ec7e5bc609529821/0x5d5bb5bdb7a228fd2f0f90c5ec7e5bc609529821-cfg-verifier.dfy: errors:        0
0x5d5bb5bdb7a228fd2f0f90c5ec7e5bc609529821: Success
build/proofs/etherscan/0x1a0205cd3fa5b3d8a11444a14b6c0fc993c2dc14/0x1a0205cd3fa5b3d8a11444a14b6c0fc993c2dc14-cfg-verifier.dfy: errors:        0
0x1a0205cd3fa5b3d8a11444a14b6c0fc993c2dc14: Success
build/proofs/etherscan/0xDcfCcaf54CB8c7c30bb7959929AbA24bF136FF57/0xDcfCcaf54CB8c7c30bb7959929AbA24bF136FF57-cfg-verifier.dfy: errors:        0
0xDcfCcaf54CB8c7c30bb7959929AbA24bF136FF57: Success
build/proofs/etherscan/0x5b348ec54c290683697f6a812ca1bfbb0e74c70d/0x5b348ec54c290683697f6a812ca1bfbb0e74c70d-cfg-verifier.dfy: errors:        0
0x5b348ec54c290683697f6a812ca1bfbb0e74c70d: Success
...
```
The number of failed verification can be obtained with the following command:
```zsh 
root@09b31c7a9d50:/# ./collectEtherscanResults.sh etherscan/success_files_1_100.txt | grep Failure | wc -l
 0
root@09b31c7a9d50:/#
```

Finally, the verification times can be consolidated with the following command:
```zsh
root@09b31c7a9d50:/# python3 ./compute-verif-time-for-list-of-files.py etherscan/success_files_1_100.txt t.txt
...
file 0x325b549a92ffcaaa5dc90a77bc8b37c69268a1e9 0:00:52.885215
file 0x4fb610a0be1965b943ee17df7c7d80071835e056 0:00:09.718108
file 0x790888d358963e0dd6ad3036cf40db2297f4d5f8 0:01:01.541117
file 0xA651332Bf73905c326bdA4549A59c05Aa3bF7DA0 0:00:44.060206
file 0x317649779b7ca2fa139c79c3628e11da92d6a91b 0:00:52.337053
file 0x4502e675bda0a3e86eb7dc2ed5cb7c9465aa6ea8 0:01:09.235403
file 0x8F18602AF63138fB598772410BFB2514746f61E0 0:01:16.835714
file 0xe743a92cf9ec592593055a6d4bf940c645db2e61 0:00:44.259891
file 0x6705c9f03763d0b509c5d4aa5144963cb7641dd9 0:00:38.348125
file 0x9264Ac4E52EDdb5D0fb345CAE8E47A8b420a96fd 0:00:34.616653
file 0xdf3a6e9bb8980666d4b6e94897487715f6b96132 0:01:25.287386
file 0x57e5112c8741fa606e344c19a73679a671a8ffd2 0:01:27.743567
file 0xbbA444b7201AfE9911BeA144907187EbB1184f7C 0:01:29.433966
file 0x9f22c4b3Dbe693a34f2aF61a16a022F87d9499EE 0:00:00.077550
file 0x203b87e9b22a1b27a684cdb923d7646b12e39760 0:00:05.731754
file 0xf365cfabd90a1f954d377d3be32e4e251dcb0d95 0:01:00.696350
file 0x84e24271c69e1cd4574432ea2177e2d2b6ea04cd 0:01:01.211748
```
which indicates the duration of the verification for each benchmark. (0:01:01.541117 is 1 minute 1 second).

## Verifying the simulation proof

The simulation proof is available in the `src/dafny/AbstractSemantics/SimulationProof.dfy` file.
It can be verified with the command:
```zsh
root@182b4415675f:/tacas25/evm-dis# dafny verify src/dafny/AbstractSemantics/SimulationProof.dfy
/tacas25/evm-dafny/src/dafny/util/int.dfy(303,26): Warning: The {:verify false} attribute should only be used during development. Consider using a bodyless lemma together with the {:axiom} attribute instead
    |
303 |     lemma {:verify false} LemmaToFromBytes(bytes:seq<u8>)
           ^^^^^^^^^^^^^^^^^^^^^^^^
...
/tacas25/evm-dafny/src/dafny/bytecode.dfy(448,29): Warning: The {:verify false} attribute should only be used during development. Consider using a bodyless function together with the {:axiom} attribute instead
    |
448 |     function {:verify false} And(st: ExecutingState): (st': State)
    |                              ^^^

/tacas25/evm-dafny/src/dafny/bytecode.dfy(487,29): Warning: The {:verify false} attribute should only be used during development. Consider using a bodyless function together with the {:axiom} attribute instead
    |
487 |     function {:verify false} Xor(st: ExecutingState): (st': State)
    |                              ^^^

Dafny program verifier finished with 46 verified, 0 errors
Compilation failed because warnings were found and --allow-warnings is false
root@182b4415675f:/tacas25/evm-dis#
```

Note that the command generates several _warnings_ that are not errors and originate from the Dafny-EVM code.
The warnings are related to the use of the `{:verify false}` attribute in the Dafny code for the Dafny-EVM.Note That these functions have been verified in the past, and the `{:verify false}` attribute may have been set to reduce the verification time. The Dafny_EVM is not part of this project and maintained independently.

## Front-end, web interface

A front end is provided at [https://bytespector.org](https://bytespector.org).
To use the front-end, paste the code in `.evm` files into the input tab.
