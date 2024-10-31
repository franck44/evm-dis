
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
evm-dis git:(main) ✗ docker run -it tacas25
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
Max depth size: 100
Shortname:  simpleCall.bin
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

## Front-end, web interface

A front end is provided at [https://bytespector.org](https://bytespector.org).
To use the front-end, paste the code in `.evm` files into the input tab.
