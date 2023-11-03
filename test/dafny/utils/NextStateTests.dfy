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


include "../../../src/dafny/utils/State.dfy"
include "../../../src/dafny/utils/Instructions.dfy"
  // include "../utils/MiscTypes.dfy"
include "../../../src/dafny/disassembler/OpcodeDecoder.dfy"
include "../../../src/dafny/utils/int.dfy"
  // include "../../../src/dafny/disassembler/OpcodeDecoder.dfy"

/**
  * Test correct computation of back propagation of a given position.
  * 
  */
module PosTrackerTests {

  //   import opened EVMOpcodes
  import opened MiscTypes
  import opened OpcodeDecoder
  import opened EVMConstants
  import opened Instructions
  import Int
  import opened State

  /** Arithmetic instruction. Proofs. */
  method Ariths(k: nat, op: Int.u8, s: ValidState)
    requires ADD <= op <= SIGNEXTEND
  {
    {
      var i := Instruction(Decode(op));
      assert i.NextState(s, true).Error?;
    }
    {
      var i := Instruction(Decode(op));
      if s.Size() >= 2 {
        assert i.NextState(s, false).EState?;
        assert i.NextState(s, false).PC() == s.PC() + 1;
        assert i.NextState(s, false).Size() == s.Size() - 1;
        assert i.NextState(s, false).stack[1..] == s.stack[2..];
      } else {
        assert i.NextState(s, false).Error?;
      }
    }
  }

  /** Concrete tests. */
  method {:test} ArithsTests()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
      var i := Instruction(Decode(ADD));
      expect i.NextState(s, false).EState?;
      expect i.NextState(s, true).Error?;
      expect  i.NextState(s, false).pc == 5;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(SIGNEXTEND));
      expect i.NextState(s, true).Error?;
      expect i.NextState(s, false).Error?;
    }
  }

  /** Comparison instructions. */
  method Comps1(k: nat, op: Int.u8)
    requires LT <= op <= ISZERO
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(op));
      assert i.NextState(s, true).Error?;
      assert op != ISZERO ==>  i.NextState(s, false).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
      var i := Instruction(Decode(op));
      assert i.NextState(s, true).Error?;
      assert i.NextState(s, false).EState?;
    }
  }


  /** Concrete tests. */
  method {:test} CompsTests()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(LT));
      assert i.NextState(s, true).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Value(10)]);
      var i := Instruction(Decode(LT));
      assert i.NextState(s, true).Error?; 
      assert i.NextState(s, false).EState?; 
      expect  i.NextState(s, false).pc == 5;
    }

    {
      var i := Instruction(Decode(EQ));
      var r := i.StackPosBackWardTracker(0);
      expect r.Left?;
    }

    {
      var i := Instruction(Decode(ISZERO));
      var r := i.StackPosBackWardTracker(0);
      expect r.Left?;
    }

    {
      var i := Instruction(Decode(SLT));
      var r := i.StackPosBackWardTracker(2);
      expect r == Right(3);
    }

    {
      var i := Instruction(Decode(ISZERO));
      var r := i.StackPosBackWardTracker(12);
      expect r == Right(12);
    }
  }

  // for k := AND to XOR
  // {
  //   var i := Decode(k);
  //   var r1 := i.StackEffect();
  //   var r2 := i.WeakestPreOperands(0);
  //   var r3 := i.WeakestPreCapacity(0);
  //   expect r1 == -1;
  //   expect r2 == 2;
  //   expect r3 == 0;
  // }

  //     {
  //       var i := Decode(NOT);
  //       var r1 := i.StackEffect();
  //       var r2 := i.WeakestPreOperands(0);
  //       var r3 := i.WeakestPreCapacity(0);
  //       expect r1 == 0;
  //       expect r2 == 1;
  //       expect r3 == 0;
  //     }

  //     for k := BYTE to SAR
  //     {
  //       var i := Decode(k);
  //       var r1 := i.StackEffect();
  //       var r2 := i.WeakestPreOperands(0);
  //       var r3 := i.WeakestPreCapacity(0);
  //       expect r1 == -1;
  //       expect r2 == 2;
  //       expect r3 == 0;
  //     }

  //   }

  /** Env instructions. */
  //   method {:test} Keccak()
  //   {
  //     var i := Decode(KECCAK256);
  //     var r1 := i.StackEffect();
  //     var r2 := i.WeakestPreOperands(0);
  //     var r3 := i.WeakestPreCapacity(0);
  //     expect r1 == - 1;
  //     expect r2 == 2;
  //     expect r3 == 0;
  //   }

  //   /** Env instructions. */
  //   method {:test} Env()
  //   {
  //     for k := ADDRESS to BASEFEE
  //     {
  //       var i := Decode(k);
  //       var r1 := i.StackEffect();
  //       var r2 := i.WeakestPreOperands(0);
  //       var r3 := i.WeakestPreCapacity(0);
  //       expect r1 == 1;
  //       expect r2 == 0;
  //       expect r3 == 1;
  //     }
  //   }

  /** Memory instructions. */
  //   method {:test} Mem()
  //   {
  //     var i := Decode(MLOAD);
  //     var r1 := i.StackEffect();
  //     var r2 := i.WeakestPreOperands(0);
  //     var r3 := i.WeakestPreCapacity(0);
  //     expect r1 == 0;
  //     expect r2 == 1;
  //     expect r3 == 0;

  //     for k := MSTORE to MSTORE8
  //     {
  //       var i := Decode(k);
  //       var r1 := i.StackEffect();
  //       var r2 := i.WeakestPreOperands(0);
  //       var r3 := i.WeakestPreCapacity(0);
  //       expect r1 == - 2;
  //       expect r2 == 2;
  //       expect r3 == 0;
  //     }
  //   }

  /** Storage instructions. */
  //   method {:test} Sto()
  //   {
  //     {
  //       var i := Decode(SLOAD);
  //       var r1 := i.StackEffect();
  //       var r2 := i.WeakestPreOperands(0);
  //       var r3 := i.WeakestPreCapacity(0);
  //       expect r1 == 0;
  //       expect r2 == 1;
  //       expect r3 == 0;
  //     }

  //     {
  //       var i := Decode(SSTORE);
  //       var r1 := i.StackEffect();
  //       var r2 := i.WeakestPreOperands(0);
  //       var r3 := i.WeakestPreCapacity(0);
  //       expect r1 == - 2;
  //       expect r2 == 2;
  //       expect r3 == 0;
  //     }
  //   }

  /** Jump instructions. */
  method Jumps(k: nat)
  {
    {
      var i := Instruction(Decode(JUMP));
      var r := i.StackPosBackWardTracker(k);
      assert r == Right(k + 1);
    }

    {
      var i := Instruction(Decode(JUMPI));
      var r := i.StackPosBackWardTracker(k);
      assert r == Right(k + 2);
    }

  }

  /** Run instructions. */
  //   method {:test} Runs()
  //   {
  //     for k := PC to GAS
  //     {
  //       var i := Decode(k);
  //       var r1 := i.StackEffect();
  //       var r2 := i.WeakestPreOperands(0);
  //       var r3 := i.WeakestPreCapacity(0);
  //       expect r1 == 1;
  //       expect r2 == 0;
  //       expect r3 == 1;
  //     }
  //   }


  /** Pop and Push instructions. */
  method PopAndPush(k: nat, offset: nat, arg: seq<char>)
    requires 0 <= offset <= 32
  {
    {
      var i := Instruction(Decode(POP));
      var r := i.StackPosBackWardTracker(k);
      assert r == Right(k + 1);
    }
    {
      var i := Instruction(Decode(PUSH0 + (offset) as Int.u8), arg);
      var r := i.StackPosBackWardTracker(k);
      if k == 0 {
        assert r == Left(arg);
      } else {
        assert r == Right(k - 1);
      }
    }
  }

  /** Duplicate instructions. */
  method Dup(k: nat, offset: nat)
    requires 0 <= offset <= 15
  {
    var i := Instruction(Decode(DUP1 + (offset) as Int.u8));
    var r := i.StackPosBackWardTracker(k);
    if k == 0 {
      assert r == Right(offset);
    } else {
      assert r == Right(k - 1);
    }
  }

  /** Swap instructions. */
  method Swap(k: nat, offset: nat)
    requires 0 <= offset <= 15
  {
    var i := Instruction(Decode(SWAP1 + (offset) as Int.u8));
    var r := i.StackPosBackWardTracker(k);

    if k == 0 {
      assert r == Right(offset + 1);
    } else if k == offset + 2 {
      assert r == Right(0);
    } else {
      assert r == Right(k);
    }
  }

  /** Log instructions. */
  //   method {:test} Log()
  //   {
  //     for k := LOG0 to LOG4
  //     {
  //       var i := Decode(k);
  //       var r1 := i.StackEffect();
  //       var r2 := i.WeakestPreOperands(0);
  //       var r3 := i.WeakestPreCapacity(0);
  //       expect r1 == - ((k - LOG0) as nat + 2);
  //       expect r2 as int == (k - LOG0) as nat + 2;
  //       expect r3 == 0;
  //     }
  //   }

  /** Return instruction. */
  //   method {:test} Return()
  //   {
  //     {
  //       var i := Decode(RETURN);
  //       var r1 := i.StackEffect();
  //       var r2 := i.WeakestPreOperands(0);
  //       var r3 := i.WeakestPreCapacity(0);
  //       expect r1 == 0;
  //       expect r2 == 2;
  //       expect r3 == 0;
  //     }
  //   }

  /** Revert instruction. */
  //   method {:test} Revert()
  //   {
  //     {
  //       var i := Decode(REVERT);
  //       var r1 := i.StackEffect();
  //       var r2 := i.WeakestPreOperands(0);
  //       var r3 := i.WeakestPreCapacity(0);
  //       expect r1 == 0;
  //       expect r2 == 2;
  //       expect r3 == 0;
  //     }
  //   }


}

