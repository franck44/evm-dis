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

/**
  * Test correct computation of next State.
  * 
  */
module NextStateTests {

  import opened MiscTypes
  import opened OpcodeDecoder
  import opened EVMConstants
  import opened Instructions
  import Int
  import opened State
  import opened StackElement

  /** Arithmetic instruction. Proofs. */
  method Ariths(k: nat, op: Int.u8, s: ValidState)
    requires ADD <= op <= SIGNEXTEND
  {
    {
      var i := Instruction(Decode(op));
      assert i.op.opcode != JUMPI;
      // following should bnot verify, precond not satisfied
      //   var n := i.NextState(s, [], 1);
    }
    {
      reveal Instruction.NextState();
      var i := Instruction(Decode(op));
      if s.Size() >= 2 {
        assert i.NextState(s, [], 0).EState?;
        assert i.NextState(s, [], 0).PC() == s.PC() + 1;
        assert i.NextState(s, [], 0).Size() == s.Size() - 1;
        assert i.NextState(s, [], 0).stack[1..] == s.stack[2..];
      } else {
        assert i.NextState(s, [], 0).Error?;
      }
    }
  }

  /** Concrete tests. */
  method {:test} ArithsTests()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
      var i := Instruction(Decode(ADD));
      expect i.NextState(s, [],  0).EState?;
      expect  i.NextState(s, [],  0).pc == 5;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(SIGNEXTEND));
      expect i.NextState(s, [],  0).Error?;
    }
  }

  /** Comparison instructions. */
  method Comps1(k: nat, op: Int.u8)
    requires LT <= op <= ISZERO
  {
    reveal Instruction.NextState();
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(op));
      assert op != ISZERO ==>  i.NextState(s, [], 0).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
      var i := Instruction(Decode(op));
      //   assert i.NextState(s, [], 1).Error?;
      assert i.NextState(s, [], 0).EState?;
    }
  }

  /** Concrete tests. */
  method {:test} CompsTests()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(LT));
      //   assert i.NextState(s, [], 1).Error?;
    }
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Value(10)]);
      var i := Instruction(Decode(LT));
      //   assert i.NextState(s, [], 1).Error?;
      assert i.NextState(s, [], 0).EState?;
      expect  i.NextState(s, [], 0).pc == 5;
    }

    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(ISZERO));
      //   assert i.NextState(s, [], 1).Error?;
      assert i.NextState(s, [], 0).EState?;
      expect  i.NextState(s, [], 0).pc == 5;
    }
  }

  /** Bitwise operators. */
  method {:test} BitWiseTests()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(AND));
      //   assert i.NextState(s, [], 1).Error?;
    }
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Value(10)]);
      var i := Instruction(Decode(OR));
      //   assert i.NextState(s, [], 1).Error?;
      assert i.NextState(s, [], 0).EState?;
      expect  i.NextState(s, [], 0).pc == 5;
      expect  i.NextState(s, [], 0).Peek(0) == Random();
    }

    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(NOT));
      //   assert i.NextState(s, [], 1).Error?;
      assert i.NextState(s, [], 0).EState?;
      expect  i.NextState(s, [], 0).pc == 5;
      expect  i.NextState(s, [], 0).Peek(0) == Random();
    }
  }

  /**   Keccak.  */
  method {:test} KeccakTests()
  {
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(KECCAK256));
      assert i.NextState(s, [], 0).Error?;
      //   assert i.NextState(s, [], 1).Error?;
    }
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
      var i := Instruction(Decode(KECCAK256));
      assert i.NextState(s, [], 0).EState?;
      assert i.NextState(s, [], 0).pc == 5;
      assert i.NextState(s, [], 0).Peek(0) == Random();
      //   assert i.NextState(s, [], 1).Error?;
    }
  }

  /**   Env operators. */
  method {:test} EnvTests()
  {
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(ADDRESS));
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Peek(0) == Random();
      //   expect i.NextState(s, [], 1).Error?;
    }
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(BASEFEE));
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Peek(0) == Random();
      //   expect i.NextState(s, [], 1).Error?;
    }
  }

  /**   Memory operators. */
  method {:test} MemTests()
  {
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random(), Value(0)]);
      var i := Instruction(Decode(MSTORE));
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Peek(0) == Value(0);
      //   expect i.NextState(s, [], 1).Error?;
    }
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(MSTORE8));
      expect i.NextState(s, [], 0).Error?;
      //   expect i.NextState(s, [], 1).Error?;
    }
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(MLOAD));
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Peek(0) == Random();
      //   expect i.NextState(s, [], 1).Error?;
    }
  }

  /**   Storage operators. */
  method {:test} StorageTests()
  {
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random(), Value(10)]);
      var i := Instruction(Decode(SSTORE));
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Peek(0) == Value(10);
      //   expect i.NextState(s, [], 1).Error?;
    }
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(SSTORE));
      expect i.NextState(s, [], 0).Error?;
      //   expect i.NextState(s, [], 1).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(SLOAD));
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Peek(0) == Random();
      //   expect i.NextState(s, [], 1).Error?;
    }
  }

  /** Runtime operators. */
  method {:test} RunTests()
  {
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(PC));
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Peek(0) == Random();
      //   expect i.NextState(s, [], 1).Error?;
    }
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(GAS));
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Peek(0) == Random();
      //   expect i.NextState(s, [], 1).Error?;
    }
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(MSIZE));
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Peek(0) == Random();
      //   expect i.NextState(s, [], 1).Error?;
    }
  }

  /**   Push k */
  method {:test} PushTests1()
  {
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(PUSH1), "09");
      assert |i.arg| == 2 * (i.op.opcode - PUSH0) as nat;
      assert forall k:: 0 <= k < |i.arg| ==> Hex.IsHex(i.arg[k]);
      assert i.IsValid();
      //   expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s,  [0x09], 0).EState?;
      expect i.NextState(s,  [0x09], 0).pc == 6;
      expect i.NextState(s,  [0x09], 0).Peek(0) == Value(9);
    }
  }

  method {:test} PushTests2()
  {
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(2)]);
      var i := Instruction(Decode(PUSH5), "0900000011");
      assert i.IsValid();
      //   expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [0x01, 0x0900000011 ], 0 ).EState?;
      expect i.NextState(s, [0x01, 0x0900000011 ], 0 ).pc == 10;
      expect i.NextState(s, [0x01, 0x0900000011 ], 0 ).Peek(0) == Value(0x0900000011);
      expect i.NextState(s, [0x01, 0x0900000011 ], 0 ).Peek(1) == Value(2);
    }
  }

  method {:test} PushTests3()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(2)]);
      var i := Instruction(Decode(PUSH2), "1122");
      assert i.IsValid();
      expect i.NextState(s, [0x0022], 0).EState?;
      expect i.NextState(s, [0x0022], 0).stack == [Random(), Value(2)];
    }
  }

  /**   POP  */
  method {:test} PopTests()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(POP));
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(POP));
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Size() == 0;
    }

    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(2), Value(3)]);
      var i := Instruction(Decode(POP));
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Size() == 1;
      expect i.NextState(s, [], 0).Peek(0) == Value(3);
    }
  }

  /**   DUP  */
  method {:test} DupTests()
  {
    {
      reveal Instruction.NextState();
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := seq(5, i requires 0 <= i < 5 => Value(i as Int.u256)));
      var i := Instruction(Decode(DUP5));
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).Peek(0) == Value(4);
    }
    reveal Instruction.NextState();

    for k: Int.u8 := 0 to 15 {
      var size := k as nat + 1;
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := seq(size, i requires 0 <= i < size => Value(i as Int.u256)));
      var i := Instruction(Decode(DUP1 + k));
      assert i.op.opcode != JUMPI;
      //   expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).Peek(0) == Value(k as Int.u256);
    }
    for k: Int.u8 := 0 to 15 {
      var size := k as nat;
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := seq(size, i requires 0 <= i < size => Value(i as Int.u256)));
      var i := Instruction(Decode(DUP1 + k));
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).Error?;
    }
  }

  /**   SWAP */
  method {:test} SwapTests()
  {
    for k: Int.u8 := 0 to 15 {
      var size := k as nat + 1;
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := seq(size, i requires 0 <= i < size => Value(i as Int.u256)));
      var i := Instruction(Decode(SWAP1 + k));
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).Error?;
    }
    for k: Int.u8 := 0 to 15 {
      var size := k as nat + 2;
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := seq(size, i requires 0 <= i < size => Value(i as Int.u256)));
      var i := Instruction(Decode(SWAP1 + k));
      assert i.op.opcode != JUMPI;
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
      expect i.NextState(s, [], 0).Size() == k as nat + 2;
      expect i.NextState(s, [], 0).Peek(k as nat + 1) == Value(0);
      expect i.NextState(s, [], 0).Peek(0) == Value(k as Int.u256 + 1);
    }
  }

  /**   Jump instructions.
    *   Reminder: jump woth condition false is an error.
    *   Only true condition is valid for JUMP.
    */
  method {:test} Jumps()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random()]);
      var i := Instruction(Decode(JUMP));
      expect i.NextState(s, [], 0).Error?;
      // expect i.NextState(s, [], 1).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(JUMP));
      expect i.NextState(s, [], 0).Error?;
      // expect i.NextState(s, [], 1).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(10), Random()]);
      var i := Instruction(Decode(JUMP));
      expect i.NextState(s, [], 0).EState?;
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).pc == 10;
    }
  }

  /**   JUMPDEST */
  method {:test} JumpDests()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(JUMPDEST));
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
    }
  }

  /**   JUMPI */
  method {:test} JumpIs()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(JUMPI));
      expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(1)]);
      var i := Instruction(Decode(JUMPI));
      expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Random(), Random()]);
      var i := Instruction(Decode(JUMPI));
      expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := [Value(10), Random()]);
      var i := Instruction(Decode(JUMPI));
      expect i.NextState(s, [], 1).EState?;
      expect i.NextState(s, [], 1).pc == 10;
      expect i.NextState(s, [], 0).EState?;
      expect i.NextState(s, [], 0).pc == 5;
    }
  }

  /**   RJUMP (not implemented an result in Error). */
  method {:test} RJumps()
  {
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(RJUMPI));
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).Error?;
    }
    {
      var s := DEFAULT_VALIDSTATE.(pc := 4, stack := []);
      var i := Instruction(Decode(RJUMPV));
      // expect i.NextState(s, [], 1).Error?;
      expect i.NextState(s, [], 0).Error?;
    }
  }

}

