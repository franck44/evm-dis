include "../../../../../../evm-dafny/src/dafny/state.dfy"
include "../../../../../../evm-dafny/src/dafny/bytecode.dfy"

module EVMProofObject {

  import opened Int
  import EvmState
  import opened Bytecode
    /** Set of valid JUMPDESTS for this program. */
  const VALID_JUMPDESTS: set<u256> := {0x3,0x14,0x17,0x2c}

  /** Lemma for Jumpdest */
  lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)
    ensures forall k:: k in VALID_JUMPDESTS ==> s.IsJumpDest(k)

  /** Node 0
    * Segment Id for this node is: 0
    * Starting at 0x0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} ExecuteFromCFGNode_s0(s0: EvmState.ExecutingState, gas: nat): (s': EvmState.State)
    // PC requirement for this node.
    requires s0.PC() == 0x0 as nat
    // Stack requirements for this node.
    requires s0.Operands() == 0
    requires s0.Capacity() >= 2

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := Push1(s0, 0x01);
      ValidJumpDest(s1);
      var s2 := Push0(s1);
      // jump to the successor Next() or Tgt of JUMP;
      ExecuteFromCFGNode_s1(s2, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0x3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} ExecuteFromCFGNode_s1(s0: EvmState.ExecutingState, gas: nat): (s': EvmState.State)
    // PC requirement for this node.
    requires s0.PC() == 0x3 as nat
    // Stack requirements for this node.
    requires s0.Operands() == 2
    requires s0.Capacity() >= 2

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x0a);
      var s3 := Dup(s2, 2);
      var s4 := Lt(s3);
      var s5 := Push1(s4, 0x14);
      ValidJumpDest(s5);
      var s6 := JumpI(s5);
      if s5.Peek(1) > 0 then
        ExecuteFromCFGNode_s3(s6, gas - 1)
      else
        ExecuteFromCFGNode_s2(s6, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0xb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: --2
    * Net Capacity Effect: +-2
    */
  function {:opaque} ExecuteFromCFGNode_s2(s0: EvmState.ExecutingState, gas: nat): (s': EvmState.State)
    // PC requirement for this node.
    requires s0.PC() == 0xb as nat
    // Stack requirements for this node.
    requires s0.Operands() == 2
    requires s0.Capacity() >= 0

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := Pop(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push1(s4, 0x40);
      ValidJumpDest(s5);
      var s6 := Return(s5);
      s6
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x14
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} ExecuteFromCFGNode_s3(s0: EvmState.ExecutingState, gas: nat): (s': EvmState.State)
    // PC requirement for this node.
    requires s0.PC() == 0x14 as nat
    // Stack requirements for this node.
    requires s0.Operands() == 2
    requires s0.Capacity() >= 1

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      ValidJumpDest(s2);
      var s3 := Push0(s2);
      // jump to the successor Next() or Tgt of JUMP;
      ExecuteFromCFGNode_s4(s3, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x17
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} ExecuteFromCFGNode_s4(s0: EvmState.ExecutingState, gas: nat): (s': EvmState.State)
    // PC requirement for this node.
    requires s0.PC() == 0x17 as nat
    // Stack requirements for this node.
    requires s0.Operands() == 3
    requires s0.Capacity() >= 2

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x0a);
      var s3 := Dup(s2, 2);
      var s4 := Lt(s3);
      var s5 := Push1(s4, 0x2c);
      ValidJumpDest(s5);
      var s6 := JumpI(s5);
      if s5.Peek(1) > 0 then
        ExecuteFromCFGNode_s6(s6, gas - 1)
      else
        ExecuteFromCFGNode_s5(s6, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x1f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: --1
    * Net Capacity Effect: +-1
    */
  function {:opaque} ExecuteFromCFGNode_s5(s0: EvmState.ExecutingState, gas: nat): (s': EvmState.State)
    // PC requirement for this node.
    requires s0.PC() == 0x1f as nat
    // Stack requirements for this node.
    requires s0.Operands() == 3
    requires s0.Capacity() >= 1

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := Pop(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x0a);
      var s4 := Swap(s3, 2);
      var s5 := Add(s4);
      var s6 := Swap(s5, 2);
      var s7 := Swap(s6, 1);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x03);
      ValidJumpDest(s9);
      var s10 := Jump(s9);
      // jump to the successor Next() or Tgt of JUMP;
      ExecuteFromCFGNode_s1(s10, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} ExecuteFromCFGNode_s6(s0: EvmState.ExecutingState, gas: nat): (s': EvmState.State)
    // PC requirement for this node.
    requires s0.PC() == 0x2c as nat
    // Stack requirements for this node.
    requires s0.Operands() == 3
    requires s0.Capacity() >= 1

    decreases gas
  {
    if gas == 0 then Revert(s0)
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Push1(s2, 0x02);
      var s4 := Mul(s3);
      var s5 := Swap(s4, 1);
      var s6 := Push1(s5, 0x17);
      ValidJumpDest(s6);
      var s7 := Jump(s6);
      // jump to the successor Next() or Tgt of JUMP;
      ExecuteFromCFGNode_s4(s7, gas - 1)
  }
}
