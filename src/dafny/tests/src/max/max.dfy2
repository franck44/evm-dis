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

include "./max-bytecode.dfy"

/**
  *  
  */
module MaxBytecodeVerification {

  import opened Int
  import opened YulStrict
  import opened YulState
  import ByteUtils
  import opened MaxBytecode

  /**
    *   A ghost (verification-only) function.
    */
  ghost function maxu256(x: u256, y: u256): (r: u256)
    ensures r == x || r == y
    ensures r >= x && r >= y
  {
    if x <= y then y else x
  }

  /**
    *  Proof of simmulation.
    *  Prove that bytecode at tag1 returns same as Max.
    *
    *  Shows that every "move" in the bytecode (AtTag ...) can be matched by a move in
    *  in the Yul code.
    *  As a result the bytecode simulates the Yul code and Yul safety properties (ensures)
    *  are enforced on the bytecode.
    *
    *  @example    Executing `ExecuteFromTag1(st)` can be matched by executing 
    *              `result := x`. After that, depending on `x < y` we can go into
    *              two different branches. Both can be matched respectively by `result := y` and 
    *              `skip` (no instruction). 
    */
  method MaxProof(x: u256, y: u256, s: Executing, ghost st:EvmState.ExecutingState) returns (result: u256, s': State, ghost st': EvmState.State)
    requires st.Operands() >= 3
    requires st.Peek(0) == x
    requires st.Peek(1) == y
    requires st.Peek(2) == tag_2 as u256
    requires st.IsJumpDest(st.Peek(2))
    requires st.PC() == tag_1 as nat
    requires st.Capacity() >= 2
    requires st.evm.memory == s.yul.memory

    ensures result == maxu256(x, y)
    ensures st'.EXECUTING?
    ensures st'.PC() == tag_2 as nat
    ensures st'.Operands() == st.Operands() - 2
    ensures st'.Peek(0) == result
    ensures st'.evm.memory == st.evm.memory
    ensures s' == s
  {
    ghost var s1 := ExecuteFromTag1(st);
    s' := s;                                          //  bytecode move
    result := x;                                      //  matching Yul move
    if YulSem.Lt(x, y) {
      st' := ExecuteFromTag4(ExecuteFromTag3(s1));     //  bytecode move
      result := y;                                    //  matching Yul move
    } else {
      st' := ExecuteFromTag4(s1);                      //  bytecode move
    }                                                 //  matching Yul move: Skip
  }

  /**
    *  Proof of simulation for Main.
    */
  method MainProof(s:  Executing, ghost st: EvmState.ExecutingState) returns (z': u256, s': State, ghost st': EvmState.State)
    requires st.Capacity() >= 5
    requires st.Operands() >= 0
    requires st.PC() == 0 as nat
    requires s.MemSize() % 32 == 0
    requires st.evm.memory == s.yul.memory

    ensures s'.RETURNS?
    ensures st'.RETURNS?
    ensures s'.data == st'.data
    ensures ByteUtils.ReadUint256(s'.data, 0) == 8
    ensures ByteUtils.ReadUint256(st'.data, 0) == 8
  {
    ValidJumpDest(st);
    ghost var st1 := ExecuteFromZero(st);        //  bytecode move
    var x := 8;                                  //  Yul move
    var y := 3;                                  //  Yul move
    assert st1.EXECUTING?;
    var z, s1, st2 := MaxProof(x, y, s, st1);    //  Simulation of call to Max.

    assert z == st2.Peek(0);
    assert s1 == s;

    st' := ExecuteFromTag2(st2);                //  Bytecode move
    z':= z;                                     //  Yul move
    var s2 := MStore(0x40, z, s1);              //  Yul move
    s' := Return(0x40, 32, s2);                 //  Yul move
  }

  method {:main} Runner() {
    // emtpy memory
    // var m := Memory.Create();
    // var m' := Main(m);

    print "Main2\n";
  }

}