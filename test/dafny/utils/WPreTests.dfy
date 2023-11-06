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


include "../../../src/dafny/utils/StackElement.dfy"
include "../../../src/dafny/utils/State.dfy"
include "../../../src/dafny/utils/Instructions.dfy"
include "../../../src/dafny/disassembler/OpcodeDecoder.dfy"
include "../../../src/dafny/utils/int.dfy"
include "../../../src/dafny/utils/WeakPre.dfy"
  /**
    * Test correct computation of next State.
    * 
    */
module WpreTests {

  import opened MiscTypes
  import opened OpcodeDecoder
  import opened EVMConstants
  import opened Instructions
  import Int
  import opened State
  import opened StackElement
  import opened WeakPre

  /** Arithmetic instruction. Proofs. */
  //   method Ariths(k: nat, op: Int.u8, s: ValidState)
  //     requires ADD <= op <= SIGNEXTEND
  //   {
  //     {
  //       var i := Instruction(Decode(op));
  //       assert i.NextState(s, true).Error?;
  //     }
  //     // {
  //     //   var i := Instruction(Decode(op));
  //     //   if s.Size() >= 2 {
  //     //     assert i.NextState(s, false).EState?;
  //     //     assert i.NextState(s, false).PC() == s.PC() + 1;
  //     //     assert i.NextState(s, false).Size() == s.Size() - 1;
  //     //     assert i.NextState(s, false).stack[1..] == s.stack[2..];
  //     //   } else {
  //     //     assert i.NextState(s, false).Error?;
  //     //   }
  //     // }
  //   }

  /** Concrete tests. */
  method {:test} ArithsTests()
  {
    {
      var c := StCond([1], [0x10]);
      var c' := Instruction(Decode(ADD)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [2];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      var c := StCond([1, 0], [0x10, 0x20]);
      var c' := Instruction(Decode(MUL)).WPre(c);
      expect c'.StFalse?;
    }
    {
      var c := StCond([1, 3, 7], [0x10, 0x20, 0x30]);
      var c' := Instruction(Decode(DIV)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [2, 4, 8];
      expect c'.TrackedVals() == c.TrackedVals();
    }
  }

  method {:test} CompsTests()
  {
    {
      var c := StCond([1], [0x10]);
      var c' := Instruction(Decode(LT)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [2];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      var c := StCond([1, 0], [0x10, 0x20]);
      var c' := Instruction(Decode(ISZERO)).WPre(c);
      expect c'.StFalse?;
    }
    {
      var c := StCond([1, 3, 7], [0x10, 0x20, 0x30]);
      var c' := Instruction(Decode(GT)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [2, 4, 8];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      var c := StCond([1, 3, 7], [0x10, 0x20, 0x30]);
      var c' := Instruction(Decode(ISZERO)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [1, 3, 7];
      expect c'.TrackedVals() == c.TrackedVals();
    }
  }

  method {:test} JumpTests()
  {
    {
      var c := StCond([1], [0x10]);
      var c' := Instruction(Decode(JUMP)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [2];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      var c := StCond([1, 0], [0x10, 0x20]);
      var c' := Instruction(Decode(JUMP)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [2, 1];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      var c := StCond([1], [0x10]);
      var c' := Instruction(Decode(JUMPI)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [3];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      var c := StCond([1, 0], [0x10, 0x20]);
      var c' := Instruction(Decode(JUMPI)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [3, 2];
      expect c'.TrackedVals() == c.TrackedVals();
    }

  }

  method {:test} PushTests1()
  {
    {
      //    no position 0 in the list
      var c := StCond([1, 4], [0x10, 0x40]);
      var c' := Instruction(Decode(PUSH0)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [0, 3];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      //    pos 0 in the list
      var c := StCond([1, 0, 4], [0x10, 0x20, 0x40]);
      //  the pushed value is the same as the tracked one.
      var c' := Instruction(Decode(PUSH1), "20").WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [0, 3];
      expect c'.TrackedVals() == [0x10, 0x40];
    }
  }

  method {:test} PushTests2()
  {
    {
      //    pos 0 in the list
      var c := StCond([1, 0, 4], [0x10, 0x20, 0x40]);
      //  the pushed value is NOT the same as the tracked one.
      var c' := Instruction(Decode(PUSH1), "21").WPre(c);
      expect c'.StFalse?;
    }
    {
      //    pos 0 only in the list
      var c := StCond([0], [0x20]);
      //  the pushed value is the same as the tracked one.
      var c' := Instruction(Decode(PUSH1), "20").WPre(c);
      expect c'.StTrue?;
    }
  }



  /** Comparison instructions. */
  //   method Comps1(k: nat, op: Int.u8)
  //     requires LT <= op <= ISZERO
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(op));
  //       assert i.NextState(s, true).Error?;
  //       assert op != ISZERO ==>  i.NextState(s, false).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
  //       var i := Instruction(Decode(op));
  //       assert i.NextState(s, true).Error?;
  //       assert i.NextState(s, false).EState?;
  //     }
  //   }

  /** Concrete tests. */
  //   method {:test} CompsTests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(LT));
  //       assert i.NextState(s, true).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Value(10)]);
  //       var i := Instruction(Decode(LT));
  //       assert i.NextState(s, true).Error?;
  //       assert i.NextState(s, false).EState?;
  //       expect  i.NextState(s, false).pc == 5;
  //     }

  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(ISZERO));
  //       assert i.NextState(s, true).Error?;
  //       assert i.NextState(s, false).EState?;
  //       expect  i.NextState(s, false).pc == 5;
  //     }
  //   }

  /** Bitwise operators. */
  //   method {:test} BitWiseTests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(AND));
  //       assert i.NextState(s, true).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Value(10)]);
  //       var i := Instruction(Decode(OR));
  //       assert i.NextState(s, true).Error?;
  //       assert i.NextState(s, false).EState?;
  //       expect  i.NextState(s, false).pc == 5;
  //       expect  i.NextState(s, false).Peek(0) == Random();
  //     }

  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(NOT));
  //       assert i.NextState(s, true).Error?;
  //       assert i.NextState(s, false).EState?;
  //       expect  i.NextState(s, false).pc == 5;
  //       expect  i.NextState(s, false).Peek(0) == Random();
  //     }
  //   }

  /**   Keccak.  */
  //   method {:test} KeccakTests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(KECCAK256));
  //       assert i.NextState(s, false).Error?;
  //       assert i.NextState(s, true).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
  //       var i := Instruction(Decode(KECCAK256));
  //       assert i.NextState(s, false).EState?;
  //       assert i.NextState(s, false).pc == 5;
  //       assert i.NextState(s, false).Peek(0) == Random();
  //       assert i.NextState(s, true).Error?;
  //     }
  //   }

  /**   Env operators. */
  //   method {:test} EnvTests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(ADDRESS));
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Peek(0) == Random();
  //       expect i.NextState(s, true).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(BASEFEE));
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Peek(0) == Random();
  //       expect i.NextState(s, true).Error?;
  //     }
  //   }

  /**   Memory operators. */
  //   method {:test} MemTests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
  //       var i := Instruction(Decode(MSTORE));
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Peek(0) == Random();
  //       expect i.NextState(s, true).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(MSTORE8));
  //       expect i.NextState(s, false).Error?;
  //       expect i.NextState(s, true).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(MLOAD));
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Peek(0) == Random();
  //       expect i.NextState(s, true).Error?;
  //     }
  //   }

  /**   Storage operators. */
  //   method {:test} StorageTests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
  //       var i := Instruction(Decode(SSTORE));
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Peek(0) == Random();
  //       expect i.NextState(s, true).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(SSTORE));
  //       expect i.NextState(s, false).Error?;
  //       expect i.NextState(s, true).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(SLOAD));
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Peek(0) == Random();
  //       expect i.NextState(s, true).Error?;
  //     }
  //   }

  /** Runtime operators. */
  //   method {:test} RunTests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
  //       var i := Instruction(Decode(PC));
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Peek(0) == Random();
  //       expect i.NextState(s, true).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
  //       var i := Instruction(Decode(GAS));
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Peek(0) == Random();
  //       expect i.NextState(s, true).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
  //       var i := Instruction(Decode(MSIZE));
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Peek(0) == Random();
  //       expect i.NextState(s, true).Error?;
  //     }
  //   }

  /**   Push k */
  //   method {:test} PushTests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(PUSH1), "09");
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 6;
  //       expect i.NextState(s, false).Peek(0) == Value(9);
  //     }

  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(2)]);
  //       var i := Instruction(Decode(PUSH10), "0900000011");
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 15;
  //       expect i.NextState(s, false).Peek(0) == Value(0x0900000011);
  //       expect i.NextState(s, false).Peek(1) == Value(2);
  //     }
  //   }

  /**   POP  */
  //   method {:test} PopTests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
  //       var i := Instruction(Decode(POP));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(POP));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Size() == 0;
  //     }

  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(2), Value(3)]);
  //       var i := Instruction(Decode(POP));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Size() == 1;
  //       expect i.NextState(s, false).Peek(0) == Value(3);
  //     }
  //   }

  /**   DUP  */
  //   method {:test} DupTests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := seq(5, i requires 0 <= i < 5 => Value(i as Int.u256)));
  //       var i := Instruction(Decode(DUP5));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).Peek(0) == Value(4);
  //     }
  //     for k: Int.u8 := 0 to 15 {
  //       var size := k as nat + 1;
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := seq(size, i requires 0 <= i < size => Value(i as Int.u256)));
  //       var i := Instruction(Decode(DUP1 + k));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).Peek(0) == Value(k as Int.u256);
  //     }
  //     for k: Int.u8 := 0 to 15 {
  //       var size := k as nat;
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := seq(size, i requires 0 <= i < size => Value(i as Int.u256)));
  //       var i := Instruction(Decode(DUP1 + k));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).Error?;
  //     }
  //   }

  /**   SWAP */
  //   method {:test} SwapTests()
  //   {
  //     for k: Int.u8 := 0 to 15 {
  //       var size := k as nat + 1;
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := seq(size, i requires 0 <= i < size => Value(i as Int.u256)));
  //       var i := Instruction(Decode(SWAP1 + k));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).Error?;
  //     }
  //     for k: Int.u8 := 0 to 15 {
  //       var size := k as nat + 2;
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := seq(size, i requires 0 <= i < size => Value(i as Int.u256)));
  //       var i := Instruction(Decode(SWAP1 + k));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //       expect i.NextState(s, false).Size() == k as nat + 2;
  //       expect i.NextState(s, false).Peek(k as nat + 1) == Value(0);
  //       expect i.NextState(s, false).Peek(0) == Value(k as Int.u256 + 1);
  //     }
  //   }

  /**   Jump instructions.
    *   Reminder: jump woth condition false is an error.
    *   Only true condition is valid for JUMP.
    */
  //   method {:test} Jumps()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
  //       var i := Instruction(Decode(JUMP));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
  //       var i := Instruction(Decode(JUMP));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(10), Random()]);
  //       var i := Instruction(Decode(JUMP));
  //       expect i.NextState(s, true).EState?;
  //       expect i.NextState(s, false).Error?;
  //       expect i.NextState(s, true).pc == 10;
  //     }
  //   }

  /**   JUMPDEST */
  //   method {:test} JumpDests()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
  //       var i := Instruction(Decode(JUMPDEST));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //     }
  //   }

  /**   JUMPI */
  //   method {:test} JumpIs()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
  //       var i := Instruction(Decode(JUMPI));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(1)]);
  //       var i := Instruction(Decode(JUMPI));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
  //       var i := Instruction(Decode(JUMPI));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(10), Random()]);
  //       var i := Instruction(Decode(JUMPI));
  //       expect i.NextState(s, true).EState?;
  //       expect i.NextState(s, true).pc == 10;
  //       expect i.NextState(s, false).EState?;
  //       expect i.NextState(s, false).pc == 5;
  //     }
  //   }

  /**   RJUMP (not implemented an result in Error). */
  //   method {:test} RJumps()
  //   {
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
  //       var i := Instruction(Decode(RJUMPI));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).Error?;
  //     }
  //     {
  //       var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
  //       var i := Instruction(Decode(RJUMPV));
  //       expect i.NextState(s, true).Error?;
  //       expect i.NextState(s, false).Error?;
  //     }
  //   }

}

