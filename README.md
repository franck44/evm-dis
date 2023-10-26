[![License](https://img.shields.io/badge/License-Apache%202.0-orange.svg)](https://opensource.org/licenses/Apache-2.0)
[![made-for-VSCode](https://img.shields.io/badge/Made%20for-VSCode-1f42ff.svg)](https://code.visualstudio.com/)

# Overview

This project provides an EVM bytecode _disassembler_.
The diassembler should support the latest opcodes like `PUSH0`, [EIP-3855](https://eips.ethereum.org/EIPS/eip-3855), and `RJump`s, [EIP-4200](https://eips.ethereum.org/EIPS/eip-4200).

The diassembler takes as an input some _binary representation_, EVM bytecode, and produces a _readable version_ of it. 
For instance the following binary string,  `prog` : 
```
600a6008600390600f565b604052005b9190808310601b575b50565b909150905f601856
```
is disassembled into the more readable (but arguably still opaque!) EVM assembly code:
```
PUSH1 0x0a
PUSH1 0x08
PUSH1 0x03
SWAP1
PUSH1 0x0f
JUMP
JUMPDEST
PUSH1 0x40
MSTORE
STOP
JUMPDEST
SWAP2
SWAP1
DUP1
DUP4
LT
PUSH1 0x1b
JUMPI
JUMPDEST
POP
JUMP
JUMPDEST
SWAP1
SWAP2
POP
SWAP1
PUSH0
PUSH1 0x18
JUMP
```

## An EVM bytecode disassembler in Dafny

The disassembler is written in [Dafny](https://github.com/dafny-lang/dafny) a verification-friendly programming language.
Some code (e.g. the definition of `EVMOpcodes`, `Int`) is adapted from the [Dafny-EVM](https://github.com/Consensys/evm-dafny) project.

## Motivations

The disassembler is a useful tool but not the ultimate goal of this project.
The main component, `Disassemble` builds a representation of the binary as a sequence of `Instructions`.
This representation can be _printed out_ (this is how the disassembler generates the readable code), but also used to generate _proof objects_ that are Dafny programs that can be verified using the [Dafny-EVM](https://github.com/Consensys/evm-dafny).

As an example, the following  [Yul](https://docs.soliditylang.org/en/latest/yul.html) code (the same can be done with Solidity code.)
```solidity
object "Runtime" {
  code {
    function checked_add_t_uint256(x, y) -> sum {
        sum := add(x, y)
        if gt(x, sum) { revert(0, 0) }
    }

    let x := 8
    let y := 56
    let z := checked_add_t_uint256(x, y)
  }
}
```
can be compiled using `solc --yul` into an (EVM) binary representation, and the result is the string `prog` given above.

The disassembler we build here will ultimately be used to generate a Dafny program to verify some properties of the previous code.
From the binary representation `prog` we want to _automatically_ build a [Dafny-EVM](https://github.com/Consensys/evm-dafny) friendly program similar to the `OverFlowCheckerBytecode` below.
This program can be used to _reason_ about the bytecode, thanks to the formal semantics provided by the  [Dafny-EVM](https://github.com/Consensys/evm-dafny) and the verification engine embedded in [Dafny](https://github.com/dafny-lang/dafny).

```rust
module OverFlowCheckerBytecode {

  import opened Int
  import EvmState
  import opened Bytecode

  /**
    *  The labels (JUMPDEST) in the bytecode.
    */
  const tag_1: u8 := 0x0c
  const tag_2: u8 := 0x0d
  const tag_3: u8 := 0x18
  const tag_4: u8 := 0x17                   //   this one is not a JUMPDEST

  /**
    *  When a JUMP or JUMPI is executed we need to make sure the target location 
    *  is a JUMPDEST.
    *  This axiom enforces it.
    */
  lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)
    ensures s.IsJumpDest(tag_1 as u256)
    ensures s.IsJumpDest(tag_2 as u256)
    ensures s.IsJumpDest(tag_3 as u256)

  /**
    *  Code starting at PC == 0.
    */
  function ExecuteFromZero(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Capacity() >= 4
    requires st.Operands() >= 0
    requires st.PC() == 0 as nat

    ensures s'.EXECUTING?
    ensures s'.PC() == tag_1 as nat
  {
    /*
    00000000: PUSH1 0xa     //  tag_2 
    00000002: PUSH1 0x8
    00000004: PUSH1 0x38
    00000006: SWAP1
    00000007: PUSH1 0xc     //  tag_1 
    00000009: JUMP
    */
    ValidJumpDest(st);
    var s1 := Push1(st, tag_2);
    var s2 := Push1(s1, 0x08);
    var s3 := Push1(s2, 0x38);
    var s4 := Swap(s3, 1);
    assert s4.Peek(2) == tag_2 as u256;
    var s5 := Push1(s4, tag_1);
    assert s5.Peek(3) == tag_2 as u256;
    var s6 := Jump(s5);
    s6
  }

  /**
    * Code staring at tag_2
    */
  function ExecuteFromTag2(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Capacity() >= 0
    requires st.Operands() >= 0
    requires st.PC() == tag_2 as nat

    ensures s'.RETURNS?
    ensures |s'.data| == 0
  {
    /*
    0000000b: STOP
    */
    var s6 := Stop(st);
    s6
  }

  /**
    * Code staring at tag_1
    */
  function ExecuteFromTag1(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Capacity() >= 1
    requires st.Operands() >= 3
    requires st.PC() == tag_1 as nat
    requires st.Peek(2) == tag_3 as u256

    ensures s'.EXECUTING?
    ensures s'.Operands() == st.Operands() - 1
    ensures s'.Peek(0) == st.Peek(2)
    ensures s'.Peek(1) as nat == (st.Peek(0) as nat + st.Peek(1) as nat) % TWO_256
    ensures s'.PC() == if st.Peek(0) > ((st.Peek(0) as nat + st.Peek(1) as nat) % TWO_256) as u256 then tag_3 as nat else tag_4 as nat
  {
    /*
    0000000c: JUMPDEST      //  tag_1
    0000000d: SWAP2
    0000000e: SWAP1
    0000000f: DUP3
    00000010: ADD
    00000011: DUP1
    00000012: SWAP3
    00000013: GT
    00000014: PUSH1 0x18    //  tag_3 
    00000016: JUMPI
    */
    ValidJumpDest(st);
    var s1 := JumpDest(st);             //  x, y, z
    var s2 := Swap(s1, 2);              //  z, y, x
    var s3 := Swap(s2, 1);              //  y, z, x
    var s4 := Dup(s3, 3);               //  x, y, z, x
    var s5 := Add(s4);                  //  x + y, z, x
    var s6 := Dup(s5, 1);               //  x + y, x + y, z, x
    var s7 := Swap(s6, 3);              //  x, x + y, z, x + y
    assert s7.Peek(0) == st.Peek(0);
    var s8 := Bytecode.Gt(s7);          //  x > x + y, z, x + y
    var s9 := Push1(s8, tag_3);         //  tag_3, x > x + y, z, x + y
    var s10 := JumpI(s9);               //  z, x + y
    s10
  }

  /**
    * Code staring at tag_3
    */
  function ExecuteFromTag3(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Operands() >= 0
    requires st.Capacity() >= 2
    requires st.PC() == tag_3 as nat

    ensures s'.ERROR?
  {
    /*
    00000018: JUMPDEST      //  tag_3 
    00000019: PUSH0
    0000001a: DUP1
    0000001b: REVERT
    */
    ValidJumpDest(st);

    var s1 := JumpDest(st);
    var s2 := Push0(s1);
    var s3 := Dup(s2, 1);

    var s4 := Revert(s3);
    s4
  }

  /**
    * Code staring at tag_3
    */
  function ExecuteFromTag4(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Operands() >= 1
    requires st.Capacity() >= 0
    requires st.PC() == tag_4 as nat
    requires st.Peek(0) in {tag_1 as u256, tag_2 as u256, tag_3 as u256}

    ensures s'.EXECUTING?
    ensures s'.PC() == st.Peek(0) as nat
    ensures s'.Operands() == st.Operands() - 1
  {
    /*
    00000017: JUMP
    */
    ValidJumpDest(st);
    // assume st.IsJumpDest(st.Peek(0));
    Jump(st)
  }
}
```

## Usage
At the moment, only a disassembler into readable EVM assembly is provided.

From Dafny, we can generate some target code in several languages. To begin with we have generated
Python and Java code.
So you don't need to install Dafny to use the disassembler, you can run the Python or java versions provided in the `build/libs`.

### Python diassembler
The Python diassembler is in `build/driver-py`.

It can be used with an input string as follows:
```zsh
evm-dis git:(main) ✗ python3 build/libs/driver-py/__main__.py                 
Not enough arguments
Usage: 
 -d <string> or <string>: disassemble <string>
 -p <string>: Proof object
 -a: both -d and -p

evm-dis git:(main) ✗ python3 build/libs/driver-py/__main__.py  "6040"
PUSH1 0x40
```
To parse a binary representation from a file `file.evm` use:
```zsh
evm-dis git:(main) ✗ python3 build/libs/driver-py/__main__.py $(<file.evm)
PUSH1 0x40

evm-dis git:(main) ✗ python3 build/libs/driver-py/__main__.py  -p "6040"      

/** Code starting at 0x0 */
function ExecuteFromTag_0(s0: EvmState.ExecutingState): (s': EvmState.State)
  requires s0.PC() == 0x0 as nat
  requires s0.Operands() >= 0
  requires s0.Capacity() >= 1
{
  ValidJumpDest(s0);
  var s1 := Push1(s0, 0x40);
  s1
}

```

### Java disassembler

The java diassembler is the file `evmdis.jar` in  `build/libs/Driver-java`.
It can be used with an input string as follows:
```zsh
evm-dis git:(main) ✗ java -jar build/libs/Driver-java/evmdis.jar              
Not enough arguments
Usage: 
 -d <string> or <string>: disassemble <string>
 -p <string>: Proof object
 -a: both -d and -p

evm-dis git:(main) ✗ java -jar build/libs/Driver-java/evmdis.jar "6040"
PUSH1 0x40
```
To parse a binary representation from a file `file.evm` use:
```zsh
evm-dis git:(main) ✗ java -jar build/libs/Driver-java/evmdis.jar $(<file.evm)
PUSH1 0x40

evm-dis git:(main) ✗ python3 build/libs/driver-py/__main__.py  -p "6040"

/** Code starting at 0x0 */
function ExecuteFromTag_0(s0: EvmState.ExecutingState): (s': EvmState.State)
  requires s0.PC() == 0x0 as nat
  requires s0.Operands() >= 0
  requires s0.Capacity() >= 1
{
  ValidJumpDest(s0);
  var s1 := Push1(s0, 0x40);
  s1
}

```
