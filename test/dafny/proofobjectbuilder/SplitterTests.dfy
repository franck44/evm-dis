/*
 * Copyright 2023 Franck Cassez
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */


include "../../../src/dafny/utils/EVMOpcodes.dfy"
include "../../../src/dafny/utils/Instructions.dfy"
include "../../../src/dafny/disassembler/OpcodeDecoder.dfy"

/**
  * Provides ability to generate Dafny code from segments.
  * 
  */
module StackEffectTests {

  import opened EVMOpcodes
  import opened MiscTypes
  import opened OpcodeDecoder
  import opened EVMConstants
  import opened Instructions

  /** Arithnmetic instructions */
  method {:test} Arith()
  {
    for k := ADD to SIGNEXTEND + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == -1;
      expect r2 == 2;
      expect r3 == 0;
    }
  }

  /** Comparison instructions. */
  method {:test} Comp()
  {
    for k := LT to EQ + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == -1;
      expect r2 == 2;
      expect r3 == 0;
    }

    {
      var i := Decode(ISZERO);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 0;
      expect r2 == 1;
      expect r3 == 0;
    }

    for k := AND to XOR + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == -1;
      expect r2 == 2;
      expect r3 == 0;
    }

    {
      var i := Decode(NOT);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 0;
      expect r2 == 1;
      expect r3 == 0;
    }

    for k := BYTE to SAR + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == -1;
      expect r2 == 2;
      expect r3 == 0;
    }

  }

  /** Env instructions. */
  method {:test} Keccak()
  {
    var i := Decode(KECCAK256);
    var r1 := i.StackEffect();
    var r2 := i.WeakestPreOperands(0);
    var r3 := i.WeakestPreCapacity(0);
    expect r1 == - 1;
    expect r2 == 2;
    expect r3 == 0;
  }

  /** Env instructions. */
  method {:test} Env()
  {
    {
      var i := Decode(ADDRESS);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 1;
      expect r2 == 0;
      expect r3 == 1;
    }
    {
      var i := Decode(BALANCE);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 0;
      expect r2 == 1;
      expect r3 == 0;
    }
    for k := ORIGIN to CALLVALUE + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 1;
      expect r2 == 0;
      expect r3 == 1;
    }
    {
      var i := Decode(CALLDATACOPY);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == -3;
      expect r2 == 3;
      expect r3 == 0;
    }
    {
      var i := Decode(CODESIZE);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 1;
      expect r2 == 0;
      expect r3 == 1;
    }
    {
      var i := Decode(CODECOPY);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == -3;
      expect r2 == 3;
      expect r3 == 0;
    }
    {
      var i := Decode(GASPRICE);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 1;
      expect r2 == 0;
      expect r3 == 1;
    }
    {
      var i := Decode(EXTCODESIZE);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 0;
      expect r2 == 1;
      expect r3 == 0;
    }
    {
      var i := Decode(EXTCODECOPY);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == -4;
      expect r2 == 4;
      expect r3 == 0;
    }
    {
      var i := Decode(RETURNDATASIZE);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 1;
      expect r2 == 0;
      expect r3 == 1;
    }
     {
      var i := Decode(RETURNDATACOPY);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == -3;
      expect r2 == 3;
      expect r3 == 0;
    }
    for k := EXTCODEHASH to BLOCKHASH + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 0;
      expect r2 == 1;
      expect r3 == 0;
    }
    for k := COINBASE to BASEFEE + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 1;
      expect r2 == 0;
      expect r3 == 1;
    }
  }

  /** Memory instructions. */
  method {:test} Mem()
  {
    var i := Decode(MLOAD);
    var r1 := i.StackEffect();
    var r2 := i.WeakestPreOperands(0);
    var r3 := i.WeakestPreCapacity(0);
    expect r1 == 0;
    expect r2 == 1;
    expect r3 == 0;

    for k := MSTORE to MSTORE8 + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == - 2;
      expect r2 == 2;
      expect r3 == 0;
    }
  }

  /** Storage instructions. */
  method {:test} Sto()
  {
    {
      var i := Decode(SLOAD);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 0;
      expect r2 == 1;
      expect r3 == 0;
    }

    {
      var i := Decode(SSTORE);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == - 2;
      expect r2 == 2;
      expect r3 == 0;
    }
  }

  /** Jump instructions. */
  method {:test} Jumps()
  {
    {
      var i := Decode(JUMP);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == - 1;
      expect r2 == 1;
      expect r3 == 0;
    }

    {
      var i := Decode(JUMPI);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == - 2;
      expect r2 == 2;
      expect r3 == 0;
    }
  }

  /** Run instructions. */
  method {:test} Runs()
  {
    for k := PC to GAS + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 1;
      expect r2 == 0;
      expect r3 == 1;
    }
  }


  /** Pop and Push instructions. */
  method {:test} PopAndPush()
  {
    var i := Decode(POP);
    var r1 := i.StackEffect();
    var r2 := i.WeakestPreOperands(0);
    var r3 := i.WeakestPreCapacity(0);
    expect r1 == - 1;
    expect r2 == 1;
    expect r3 == 0;

    for k := PUSH0 to PUSH32 + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 1;
      expect r2 == 0;
      expect r3 == 1;
    }
  }

  /** Duplicate instructions. */
  method {:test} Dup()
  {
    for k := DUP1 to DUP16 + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 1;
      expect r2 as int == (k - DUP1) as nat + 1;
      expect r3 == 1;
    }
  }

  /** Swap instructions. */
  method {:test} Swap()
  {
    for k := SWAP1 to SWAP16 + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 0;
      expect r2 as int == (k - SWAP1) as nat + 2;
      expect r3 == 0;
    }
  }

  /** Log instructions. */
  method {:test} Log()
  {
    for k := LOG0 to LOG4 + 1
    {
      var i := Decode(k);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == - ((k - LOG0) as nat + 2);
      expect r2 as int == (k - LOG0) as nat + 2;
      expect r3 == 0;
    }
  }

  /** Return instruction. */
  method {:test} Return()
  {
    {
      var i := Decode(RETURN);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 0;
      expect r2 == 2;
      expect r3 == 0;
    }
  }

  /** Revert instruction. */
  method {:test} Revert()
  {
    {
      var i := Decode(REVERT);
      var r1 := i.StackEffect();
      var r2 := i.WeakestPreOperands(0);
      var r3 := i.WeakestPreCapacity(0);
      expect r1 == 0;
      expect r2 == 2;
      expect r3 == 0;
    }
  }


}

