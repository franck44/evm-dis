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

include "../../../../libs/evm-dafny/src/dafny/state.dfy"
include "../../../../libs/evm-dafny/src/dafny/evm.dfy"

include "../../Yul/Semantics.dfy"
include "../../Yul/StrictSemantics.dfy"
include "../../Yul/State.dfy"

/**
  *  
  */
module MaxBytecode {

  import opened Int
    //   import opened YulSem = YulStrict
    //   import opened YulState
  import opened Opcode
  import EvmState
  import Memory
  import EVM
  import opened Bytecode
  import Gas

  /**
    *  The labels (JUMPDEST) in the bytecode.
    */
  const tag_1: u8 := 0x13
  const tag_2: u8 := 0x0a
  const tag_3: u8 := 0x1f
  const tag_4: u8 := 0x1c

  /**
    *  When a JUMP or JUMPI is executed we need to make sure the target location 
    *  is a JUMPDEST.
    *  This axiom enforces it.
    */
  lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)
    ensures s.IsJumpDest(tag_1 as u256)
    ensures s.IsJumpDest(tag_2 as u256)
    ensures s.IsJumpDest(tag_3 as u256)
    ensures s.IsJumpDest(tag_4 as u256)
    
  /**
    *  Code starting at PC == 0.
    */
  function ExecuteFromZero(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Capacity() >= 5
    requires st.Operands() >= 0
    requires st.PC() == 0 as nat

    ensures s'.EXECUTING?
    ensures s'.PC() == tag_1 as nat
  {
    /*
    00000000: PUSH1 0xa     //  tag_2 
    00000002: PUSH1 0x8
    00000004: PUSH1 0x3
    00000006: SWAP1
    00000007: PUSH1 0xf     //  tag_1 
    00000009: JUMP
    */
    ValidJumpDest(st);
    var s1 := Push1(st, tag_2);
    var s2 := Push1(s1, 0x08);
    var s3 := Push1(s2, 0x03);
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
    requires st.Capacity() >= 1
    requires st.Operands() >= 1
    requires st.PC() == tag_2 as nat

    ensures s'.RETURNS?
    ensures |s'.data| == 32
  {
    /*
    0000000a: JUMPDEST
    0000000b: PUSH1 0x40
    0000000d: MSTORE
    0000000e: PUSH1 0x20
    00000010: PUSH1 0x40
    00000012: RETURN    
    */
    var s1 := JumpDest(st);
    var s2 := Push1(s1, 0x40);
    var s3 := Bytecode.MStore(s2);
    assert s3.EXECUTING?;
    var s4 := Push1(s3, 0x20);
    var s5 := Push1(s4, 0x40);
    var s6 := Return(s5);
    s6
  }

  /**
    * Code staring at tag_1.
    * Code of the max function.
    */
  function ExecuteFromTag1(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Capacity() >= 2
    requires st.Operands() >= 3
    requires st.PC() == tag_1 as nat
    requires st.IsJumpDest(st.Peek(2))
    requires st.Peek(2) == tag_2 as u256

    ensures s'.EXECUTING?
    ensures s'.Operands() == st.Operands()
    ensures s'.Peek(0) == st.Peek(1)
    ensures s'.Peek(1) == st.Peek(2)
    ensures s'.Peek(2) == st.Peek(0)
    ensures s'.PC() == if st.Peek(0) < st.Peek(1) then tag_3 as nat else tag_4 as nat
  {
    /*
    00000013: JUMPDEST      //  tag_1(def)
    00000014: SWAP2
    00000015: SWAP1
    00000016: DUP1
    00000017: DUP4
    00000018: LT
    00000019: PUSH1 0x1f    //  tag_3 
    0000001b: JUMPI
    */
    ValidJumpDest(st);
    var s1 := JumpDest(st); //  r, y, x
    var s2 := Swap(s1, 2);  //  x, y, r
    var s3 := Swap(s2, 1);  //  x, r, y
    var s4 := Dup(s3, 1);   //  x, r, y, y
    var s5 := Dup(s4, 4);   //  x, r, y, y, x
    assert s5.PC() == 0x18;
    var s6 := Bytecode.Lt(s5);       //  x, r, y, x < y
    var s7 := Push1(s6, tag_3); //  x, r, y, x < y, tag_ 3
    var s8 := JumpI(s7);        //  x, r, y
    s8
  }

  /**
    * Code staring at tag_4
    */
  function ExecuteFromTag4(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Operands() >= 3
    requires st.PC() == tag_4 as nat
    requires st.IsJumpDest(st.Peek(1))
    requires st.Peek(1) as nat == tag_2 as nat

    ensures s'.EXECUTING?
    ensures s'.PC() == st.Peek(1) as nat == tag_2 as nat
    ensures s'.Operands() == st.Operands() - 2
    ensures s'.Peek(0) == st.Peek(2)
  {
    /*
    0000001c: JUMPDEST      // tag_4 x2, x1, x0 
    0000001d: POP           //  x2, x1 
    0000001e: JUMP          //  x2 
    */
    var s9 := JumpDest(st);
    var s10 := Pop(s9);
    assert s10.IsJumpDest(s10.Peek(0));
    var s11 := Jump(s10);
    assert s11.PC() == st.Peek(1) as nat;
    s11
  }

  /**
    * Code staring at tag_2
    */
  function ExecuteFromTag3(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Operands() >= 3
    requires st.Capacity() >= 1
    requires st.PC() == tag_3 as nat
    requires st.IsJumpDest(st.Peek(1))
    requires st.Peek(1) == tag_2 as u256

    ensures s'.EXECUTING?
    ensures s'.PC() == tag_4 as nat
    ensures s'.Operands() == st.Operands()
  {
    /*
    0000001f: JUMPDEST      //  tag_3(def)
    00000020: SWAP1
    00000021: SWAP2
    00000022: POP
    00000023: SWAP1
    00000024: PUSH0
    00000025: PUSH1 0x1c    //  jump(tag_4)
    00000027: JUMP
    */
    ValidJumpDest(st);

    var s1 := JumpDest(st);
    var s2 := Swap(s1, 1);
    var s3 := Swap(s2, 2);
    var s4 := Pop(s3);
    var s5 := Swap(s4, 1);
    var s6 := Push0(s5);
    var s7 := Push1(s6, tag_4);

    var s8 := Jump(s7);
    assert s8.Peek(0) == 0; //  x0, x1, 0
    s8
  }

  method {:main} Runner() {
    // emtpy memory
    // var m := Memory.Create();
    // var m' := Main(m);

    print "Main2\n";
  }

}