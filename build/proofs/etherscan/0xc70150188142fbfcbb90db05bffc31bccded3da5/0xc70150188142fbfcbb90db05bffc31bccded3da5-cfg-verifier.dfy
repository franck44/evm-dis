include "../../../../src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module  {:disableNonlinearArithmetic} EVMProofObject {

  import opened AbstractSemantics
  import opened AbstractState

  /** Node 0
    * Segment Id for this node is: 0
    * Starting at 0x0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s0(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x80);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := MStore(s4);
      var s6 := Push4(s5, 0x34b1f0a9);
      var s7 := Push1(s6, 0xe2);
      var s8 := Shl(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x01);
      var s12 := Push1(s11, 0x84);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Push1(s15, 0x24);
      var s17 := Dup2(s16);
      var s18 := Push20(s17, 0xfd513630f697a9c1731f196185fb9eba6eaac20b);
      var s19 := Gas(s18);
      var s20 := StaticCall(s19);
      var s21 := Push1(s20, 0x3a);
      assert s21.Peek(0) == 0x3a;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s2(s22, gas - 1)
      else
        ExecuteFromCFGNode_s1(s22, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0x36
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x3a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x80);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := CallDataSize(s5);
      var s7 := Dup2(s6);
      var s8 := Dup3(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Dup1(s9);
      var s11 := Dup2(s10);
      var s12 := CallDataSize(s11);
      var s13 := Dup4(s12);
      var s14 := Dup6(s13);
      var s15 := Gas(s14);
      var s16 := DelegateCall(s15);
      var s17 := Swap2(s16);
      var s18 := Pop(s17);
      var s19 := ReturnDataSize(s18);
      var s20 := Dup2(s19);
      var s21 := Dup3(s20);
      var s22 := ReturnDataCopy(s21);
      var s23 := Dup2(s22);
      var s24 := Dup1(s23);
      var s25 := IsZero(s24);
      var s26 := Push1(s25, 0x5b);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s4(s27, gas - 1)
      else
        ExecuteFromCFGNode_s3(s27, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x58
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Dup3(s1);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := ReturnDataSize(s1);
      var s3 := Dup3(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }
}
