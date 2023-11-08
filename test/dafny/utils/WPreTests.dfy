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
  * Test correct computation of WPre for instructions.
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

  method {:test} DupTests1()
  {
    {
      //    no position 0 in the list
      var c := StCond([1, 4], [0x10, 0x40]);
      var c' := Instruction(Decode(DUP1)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [0, 3];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      //    pos 0 in the list
      var c := StCond([1, 0, 4], [0x10, 0x20, 0x40]);
      var c' := Instruction(Decode(DUP1)).WPre(c);
      //    there is a tracked position that is DUP1 - DUP1 + 1 i.e. 1
      //    the tracked values at 1 and 0 disagree
      expect c'.StFalse?;
    }
    {
      //    pos 0 in the list
      var c := StCond([1, 0, 2], [0x10, 0x20, 0x40]);
      var c' := Instruction(Decode(DUP2)).WPre(c);
      //    there is a tracked position that is DUP2 - DUP1 + 1 i.e. 2
      //    the tracked values at 2 and 0 disagree
      expect c'.StFalse?;
    }
    {
      //    pos 0 in the list
      var c := StCond([1, 0, 4], [0x10, 0x20, 0x40]);
      var c' := Instruction(Decode(DUP2)).WPre(c);
      //    there is NO tracked position that is DUP2 - DUP1 + 1 i.e. 2
      expect c'.StCond?;
      expect c'.TrackedPos() == [0, 1, 3];
      expect c'.TrackedVals() == c.TrackedVals();
    }
  }

  method {:test} SwapTests1()
  {
    {
      //    no position 0 in the list
      var c := StCond([1, 4], [0x10, 0x40]);
      var c' := Instruction(Decode(SWAP3)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [1, 4];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      //   position 0 in the list
      var c := StCond([0, 1, 4], [0x09, 0x10, 0x40]);
      var c' := Instruction(Decode(SWAP3)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [3, 1, 4];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      //   position SWAP3 - SWAP1 + 1 == 3 in the list
      var c := StCond([7, 1, 4, 3], [0x09, 0x10, 0x40, 0x50]);
      var c' := Instruction(Decode(SWAP3)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [7, 1, 4, 0];
      expect c'.TrackedVals() == c.TrackedVals();
    }
    {
      //   0 in the list and position SWAP3 - SWAP1 + 1 == 3 in the list
      var c := StCond([0, 1, 4, 3], [0x09, 0x10, 0x40, 0x50]);
      var c' := Instruction(Decode(SWAP3)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [3, 1, 4, 0];
      expect c'.TrackedVals() == c.TrackedVals();
    }
  }

  method {:test} PopTests1()
  {
    {
      //    no position 0 in the list
      var c := StCond([1, 4], [0x10, 0x40]);
      var c' := Instruction(Decode(POP)).WPre(c);
      expect c'.StCond?;
      expect c'.TrackedPos() == [2, 5];
      expect c'.TrackedVals() == c.TrackedVals();
    }
  }

}

