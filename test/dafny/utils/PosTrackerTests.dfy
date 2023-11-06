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
  // include "../utils/MiscTypes.dfy"
include "../../../src/dafny/disassembler/OpcodeDecoder.dfy"
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/utils/StackElement.dfy"
  // include "../../../src/dafny/disassembler/OpcodeDecoder.dfy"

/**
  * Test correct computation of back propagation of a given position.
  * 
  */
module PosTrackerTests {

  import opened EVMOpcodes
  import opened MiscTypes
  import opened OpcodeDecoder
  import opened EVMConstants
  import opened Instructions
  import Int
  import opened StackElement

  /** Arithmetic instruction. Proofs. */
  method Ariths(k: nat, op: Int.u8)
    requires ADD <= op <= SIGNEXTEND
  {
    {
      var i := Instruction(Decode(op));
      var r := i.StackPosBackWardTracker(k);
      if k > 0 {
        assert r == Right(k + 1);
      } else {
        assert r.Left?;
      }
    }
  }

  /** Concrete tests. */
  method {:test} ArithsTests()
  {
    {
      var i := Instruction(Decode(ADD));
      var r := i.StackPosBackWardTracker(0);
      expect r.Left?;
    }

    {
      var i := Instruction(Decode(ADD));
      var r := i.StackPosBackWardTracker(1);
      expect r == Right(2);
    }
  }

  /** Comparison instructions. */
  method Comps1(k: nat, op: Int.u8)
    requires LT <= op <= EQ
  {
    {
      var i := Instruction(Decode(op));
      var r := i.StackPosBackWardTracker(k);
      if k >= 1 {
        assert r == Right(k + 1);
      } else {
        assert r.Left?;
      }
    }
  }

  method Comps2(k: nat, op: Int.u8)
    requires op == ISZERO
  {
    {
      var i := Instruction(Decode(op));
      var r := i.StackPosBackWardTracker(k);
      if k > 0 {
        assert r == Right(k);
      } else {
        assert r.Left?;
      }
    }
  }

  /** Concrete tests. */
  method {:test} CompsTests()
  {
    {
      var i := Instruction(Decode(GT));
      var r := i.StackPosBackWardTracker(0);
      expect r.Left?;
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

    /** Pops  */
  method Pops(k: nat)
  {
    {
      var i := Instruction(Decode(POP));
      assert i.arg == [];
      assert i.IsValid();
      assert i.op.IsValid();
      var r := i.StackPosBackWardTracker(k);
      assert r == Right(k + 1);
    }
    
  }

  /** Push instructions. */
  method Pushes(k: nat, offset: nat, arg: seq<char>)
    requires 0 <= offset <= 32
    requires |arg| <= 64 && |arg| % 2 == 0
    requires |arg| == 2 * k
    requires forall k:: 0 <= k < |arg| ==> Hex.IsHex(arg[k])
  {
    {
      var i := Instruction(Decode(PUSH0 + (offset) as Int.u8), arg);
      assert i.IsValid();
      assert i.op.IsValid();
      var r := i.StackPosBackWardTracker(k);
      if k == 0 {
        assert r == Left(Value(GetArgValuePush(arg)));
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
    } else if k == offset + 1 {
      assert r == Right(0);
    } else {
      assert r == Right(k);
    }
  }

  method {:test} SwapTests()
  {
    {
      var i := Instruction(Decode(SWAP1));
      var r := i.StackPosBackWardTracker(1);
      expect r.Right? && r.Right() == 0;
    }
    {
      var i := Instruction(Decode(SWAP1));
      var r := i.StackPosBackWardTracker(0);
      expect r.Right? && r.Right() == 1;
    }
    {
      var i := Instruction(Decode(SWAP1));
      var r := i.StackPosBackWardTracker(2);
      expect r.Right? && r.Right() == 2;
    }

    {
      var i := Instruction(Decode(SWAP11));
      var r := i.StackPosBackWardTracker(2);
      expect r.Right? && r.Right() == 2;
    }
    {
      var i := Instruction(Decode(SWAP11));
      var r := i.StackPosBackWardTracker(11);
      expect r.Right? && r.Right() == 0;
    }
    {
      var i := Instruction(Decode(SWAP11));
      var r := i.StackPosBackWardTracker(0);
      expect r.Right? && r.Right() == 11;
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

