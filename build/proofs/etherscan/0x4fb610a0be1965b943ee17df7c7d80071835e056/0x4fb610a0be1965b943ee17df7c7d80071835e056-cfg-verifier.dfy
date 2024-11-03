include "../../../../src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module  {:disableNonlinearArithmetic} EVMProofObject {

  import opened AbstractSemantics
  import opened AbstractState

  /** Node 0
    * Segment Id for this node is: 0
    * Starting at 0x0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
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
      var s1 := Push1(s0, 0x40);
      var s2 := Push1(s1, 0x80);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Swap1(s5);
      var s7 := Dup2(s6);
      var s8 := CallDataSize(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0015);
      assert s11.Peek(0) == 0x15;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s2(s12, gas - 1)
      else
        ExecuteFromCFGNode_s1(s12, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0x11
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x15
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Push1(s5, 0xe0);
      var s7 := Shr(s6);
      var s8 := Dup1(s7);
      var s9 := Push4(s8, 0x0a3b0a4f);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x02e2);
      assert s11.Peek(0) == 0x2e2;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s12, gas - 1)
      else
        ExecuteFromCFGNode_s3(s12, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x29
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x3af32abf);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02a0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s5, gas - 1)
      else
        ExecuteFromCFGNode_s4(s5, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x34
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8ab1d681);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0231);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s44(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0209);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s40(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x4a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xd86cd420);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01cb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x55
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xe43252d7);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x012a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s26(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x60
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00b9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x6b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0xf667e0aa);
      var s2 := Eq(s1);
      var s3 := Push2(s2, 0x0079);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s4, gas - 1)
      else
        ExecuteFromCFGNode_s10(s4, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 10
    * Starting at 0x75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 11
    * Segment Id for this node is: 11
    * Starting at 0x79
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Push2(s2, 0x00b5);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s4, gas - 1)
      else
        ExecuteFromCFGNode_s12(s4, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 12
    * Starting at 0x7f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := CallDataSize(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Not(s3);
      var s5 := Add(s4);
      var s6 := SLt(s5);
      var s7 := Push2(s6, 0x00b5);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s8, gas - 1)
      else
        ExecuteFromCFGNode_s13(s8, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 13
    * Starting at 0x8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataLoad(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      var s12 := Sub(s11);
      var s13 := Push2(s12, 0x00b5);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s14, gas - 1)
      else
        ExecuteFromCFGNode_s14(s14, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 14
    * Starting at 0x9e
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Dup4(s1);
      var s3 := Push2(s2, 0xffff);
      var s4 := Swap3(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap6(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x02);
      var s9 := Dup6(s8);
      var s10 := MStore(s9);
      var s11 := Keccak256(s10);
      var s12 := SLoad(s11);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Return(s18);
      // Segment is terminal (Revert, Stop or Return)
      s19
  }

  /** Node 15
    * Segment Id for this node is: 15
    * Starting at 0xb5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 16
    * Segment Id for this node is: 16
    * Starting at 0xb9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := Dup3(s2);
      var s4 := CallValue(s3);
      var s5 := Push2(s4, 0x0126);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s6, gas - 1)
      else
        ExecuteFromCFGNode_s17(s6, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 17
    * Starting at 0xc1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := CallDataSize(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Not(s3);
      var s5 := Add(s4);
      var s6 := SLt(s5);
      var s7 := Push2(s6, 0x0126);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s8, gas - 1)
      else
        ExecuteFromCFGNode_s18(s8, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 18
    * Starting at 0xcd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataLoad(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Swap2(s9);
      var s11 := Dup3(s10);
      var s12 := Swap1(s11);
      var s13 := Sub(s12);
      var s14 := Push2(s13, 0x00b5);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s15, gas - 1)
      else
        ExecuteFromCFGNode_s19(s15, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 19
    * Starting at 0xe1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Swap1(s1);
      var s3 := Push2(s2, 0x00f1);
      var s4 := Dup5(s3);
      var s5 := SLoad(s4);
      var s6 := Swap2(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Caller(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x03e7);
      assert s11.Peek(0) == 0x3e7;
      assert s11.Peek(2) == 0xf1;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s12, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 56
    * Starting at 0x3e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf1;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x03ee);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s4, gas - 1)
      else
        ExecuteFromCFGNode_s21(s4, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 57
    * Starting at 0x3ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xf1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s1, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 20
    * Starting at 0xf1
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Not(s6);
      var s8 := And(s7);
      var s9 := Or(s8);
      var s10 := Dup3(s9);
      var s11 := SStore(s10);
      var s12 := Caller(s11);
      var s13 := Push32(s12, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s14 := Dup4(s13);
      var s15 := Dup1(s14);
      var s16 := Log3(s15);
      var s17 := Dup1(s16);
      var s18 := Return(s17);
      // Segment is terminal (Revert, Stop or Return)
      s18
  }

  /** Node 23
    * Segment Id for this node is: 58
    * Starting at 0x3ee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xf1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf1;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(4) == 0xf1;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x0c);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 12, 0x15539055551213d492569151);
      var s20 := Push1(s19, 0xa2);
      var s21 := Shl(s20);
      assert s21.Peek(2) == 0xf1;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Swap1(s26);
      var s28 := Revert(s27);
      // Segment is terminal (Revert, Stop or Return)
      s28
  }

  /** Node 24
    * Segment Id for this node is: 15
    * Starting at 0xb5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 25
    * Segment Id for this node is: 21
    * Starting at 0x126
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 26
    * Segment Id for this node is: 22
    * Starting at 0x12a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x03);
      var s7 := Not(s6);
      var s8 := Add(s7);
      var s9 := SLt(s8);
      var s10 := Push2(s9, 0x00b5);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s11, gas - 1)
      else
        ExecuteFromCFGNode_s27(s11, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 23
    * Starting at 0x139
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Swap4(s10);
      var s12 := Swap2(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := Sub(s14);
      var s16 := Push2(s15, 0x01c7);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s17, gas - 1)
      else
        ExecuteFromCFGNode_s28(s17, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 24
    * Starting at 0x14f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x015c);
      assert s1.Peek(0) == 0x15c;
      var s2 := Swap1(s1);
      var s3 := Dup6(s2);
      var s4 := SLoad(s3);
      var s5 := And(s4);
      var s6 := Caller(s5);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x03e7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s9, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 56
    * Starting at 0x3e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x15c;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x03ee);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s4, gas - 1)
      else
        ExecuteFromCFGNode_s30(s4, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 57
    * Starting at 0x3ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s1, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 25
    * Starting at 0x15c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup5(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x02);
      var s6 := Push1(s5, 0x20);
      var s7 := MStore(s6);
      var s8 := Push2(s7, 0xffff);
      var s9 := Dup3(s8);
      var s10 := Dup6(s9);
      var s11 := Keccak256(s10);
      var s12 := SLoad(s11);
      var s13 := And(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x01b2);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s16, gas - 1)
      else
        ExecuteFromCFGNode_s32(s16, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 26
    * Starting at 0x172
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x172 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      var s2 := Dup5(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Swap1(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup2(s7);
      var s9 := Dup5(s8);
      var s10 := Keccak256(s9);
      var s11 := Dup1(s10);
      var s12 := SLoad(s11);
      var s13 := Push1(s12, 0xff);
      var s14 := Not(s13);
      var s15 := And(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Or(s16);
      var s18 := Swap1(s17);
      var s19 := SStore(s18);
      var s20 := Swap1(s19);
      var s21 := MLoad(s20);
      var s22 := Swap2(s21);
      var s23 := Dup3(s22);
      var s24 := MStore(s23);
      var s25 := Push32(s24, 0x4f783c179409b4127238bc9c990bc99b9a651666a0d20b51d6c42849eb88466d);
      var s26 := Swap2(s25);
      var s27 := Log1(s26);
      var s28 := Dup1(s27);
      var s29 := Return(s28);
      // Segment is terminal (Revert, Stop or Return)
      s29
  }

  /** Node 33
    * Segment Id for this node is: 27
    * Starting at 0x1b2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Push1(s2, 0x24);
      var s4 := Swap3(s3);
      var s5 := MLoad(s4);
      var s6 := Swap2(s5);
      var s7 := Push4(s6, 0x442fdff3);
      var s8 := Push1(s7, 0xe0);
      var s9 := Shl(s8);
      var s10 := Dup4(s9);
      var s11 := MStore(s10);
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Revert(s14);
      // Segment is terminal (Revert, Stop or Return)
      s15
  }

  /** Node 34
    * Segment Id for this node is: 58
    * Starting at 0x3ee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x15c;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(4) == 0x15c;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x0c);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 12, 0x15539055551213d492569151);
      var s20 := Push1(s19, 0xa2);
      var s21 := Shl(s20);
      assert s21.Peek(2) == 0x15c;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Swap1(s26);
      var s28 := Revert(s27);
      // Segment is terminal (Revert, Stop or Return)
      s28
  }

  /** Node 35
    * Segment Id for this node is: 28
    * Starting at 0x1c7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup5(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 36
    * Segment Id for this node is: 29
    * Starting at 0x1cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := CallValue(s2);
      var s4 := Push2(s3, 0x00b5);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s5, gas - 1)
      else
        ExecuteFromCFGNode_s37(s5, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 30
    * Starting at 0x1d2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := CallDataSize(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Not(s3);
      var s5 := Add(s4);
      var s6 := SLt(s5);
      var s7 := Push2(s6, 0x00b5);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s8, gas - 1)
      else
        ExecuteFromCFGNode_s38(s8, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 31
    * Starting at 0x1de
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataLoad(s0);
      var s2 := Push2(s1, 0xffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup1(s4);
      var s6 := Swap2(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x00b5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s9, gas - 1)
      else
        ExecuteFromCFGNode_s39(s9, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 32
    * Starting at 0x1eb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Push1(s3, 0x20);
      var s5 := Swap1(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Swap2(s7);
      var s9 := Dup2(s8);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      var s12 := SLoad(s11);
      var s13 := Swap1(s12);
      var s14 := MLoad(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0xa0);
      var s18 := Shl(s17);
      var s19 := Sub(s18);
      var s20 := Swap1(s19);
      var s21 := Swap2(s20);
      var s22 := And(s21);
      var s23 := Dup2(s22);
      var s24 := MStore(s23);
      var s25 := Return(s24);
      // Segment is terminal (Revert, Stop or Return)
      s25
  }

  /** Node 40
    * Segment Id for this node is: 33
    * Starting at 0x209
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x209 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := CallValue(s3);
      var s5 := Push2(s4, 0x0126);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s6, gas - 1)
      else
        ExecuteFromCFGNode_s41(s6, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 34
    * Starting at 0x211
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x211 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Push1(s1, 0x03);
      var s3 := Not(s2);
      var s4 := CallDataSize(s3);
      var s5 := Add(s4);
      var s6 := SLt(s5);
      var s7 := Push2(s6, 0x0126);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s8, gas - 1)
      else
        ExecuteFromCFGNode_s42(s8, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 35
    * Starting at 0x21c
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      var s2 := SLoad(s1);
      var s3 := Swap1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Return(s16);
      // Segment is terminal (Revert, Stop or Return)
      s17
  }

  /** Node 43
    * Segment Id for this node is: 21
    * Starting at 0x126
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 44
    * Segment Id for this node is: 36
    * Starting at 0x231
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x231 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x03);
      var s7 := Not(s6);
      var s8 := Add(s7);
      var s9 := SLt(s8);
      var s10 := Push2(s9, 0x00b5);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s11, gas - 1)
      else
        ExecuteFromCFGNode_s45(s11, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 37
    * Starting at 0x240
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x240 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Dup3(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Dup3(s13);
      var s15 := Swap1(s14);
      var s16 := Sub(s15);
      var s17 := Push2(s16, 0x01c7);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s18, gas - 1)
      else
        ExecuteFromCFGNode_s46(s18, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 38
    * Starting at 0x257
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x257 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push32(s0, 0x535611fb62fa2a833988f283b779e417e996813e44046f521d76c17b5943b08c);
      var s2 := Swap4(s1);
      var s3 := Push2(s2, 0x0288);
      var s4 := Push1(s3, 0x20);
      var s5 := Swap5(s4);
      var s6 := Dup8(s5);
      var s7 := SLoad(s6);
      var s8 := And(s7);
      var s9 := Caller(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x03e7);
      assert s11.Peek(0) == 0x3e7;
      assert s11.Peek(2) == 0x288;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s12, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 56
    * Starting at 0x3e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x288;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x03ee);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s4, gas - 1)
      else
        ExecuteFromCFGNode_s48(s4, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 57
    * Starting at 0x3ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s1, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 39
    * Starting at 0x288
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x288 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup7(s2);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup1(s6);
      var s8 := Dup6(s7);
      var s9 := Keccak256(s8);
      var s10 := Dup1(s9);
      var s11 := SLoad(s10);
      var s12 := Push1(s11, 0xff);
      var s13 := Not(s12);
      var s14 := And(s13);
      var s15 := Swap1(s14);
      var s16 := SStore(s15);
      var s17 := MLoad(s16);
      var s18 := Swap1(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Log1(s20);
      var s22 := Dup1(s21);
      var s23 := Return(s22);
      // Segment is terminal (Revert, Stop or Return)
      s23
  }

  /** Node 50
    * Segment Id for this node is: 58
    * Starting at 0x3ee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x288;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(4) == 0x288;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x0c);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 12, 0x15539055551213d492569151);
      var s20 := Push1(s19, 0xa2);
      var s21 := Shl(s20);
      assert s21.Peek(2) == 0x288;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Swap1(s26);
      var s28 := Revert(s27);
      // Segment is terminal (Revert, Stop or Return)
      s28
  }

  /** Node 51
    * Segment Id for this node is: 40
    * Starting at 0x2a0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := CallValue(s2);
      var s4 := Push2(s3, 0x00b5);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s5, gas - 1)
      else
        ExecuteFromCFGNode_s52(s5, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 41
    * Starting at 0x2a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := CallDataSize(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Not(s3);
      var s5 := Add(s4);
      var s6 := SLt(s5);
      var s7 := Push2(s6, 0x00b5);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s8, gas - 1)
      else
        ExecuteFromCFGNode_s53(s8, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 42
    * Starting at 0x2b3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      var s12 := Swap1(s11);
      var s13 := Sub(s12);
      var s14 := Push2(s13, 0x02de);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s15, gas - 1)
      else
        ExecuteFromCFGNode_s54(s15, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 43
    * Starting at 0x2c7
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      var s2 := Push1(s1, 0xff);
      var s3 := Swap3(s2);
      var s4 := Dup5(s3);
      var s5 := Swap3(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap7(s6);
      var s8 := MStore(s7);
      var s9 := Dup6(s8);
      var s10 := MStore(s9);
      var s11 := Keccak256(s10);
      var s12 := SLoad(s11);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := IsZero(s16);
      var s18 := IsZero(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Return(s20);
      // Segment is terminal (Revert, Stop or Return)
      s21
  }

  /** Node 55
    * Segment Id for this node is: 44
    * Starting at 0x2de
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 56
    * Segment Id for this node is: 45
    * Starting at 0x2e2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap3(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x03);
      var s7 := Not(s6);
      var s8 := CallDataSize(s7);
      var s9 := Add(s8);
      var s10 := SLt(s9);
      var s11 := Push2(s10, 0x03e4);
      assert s11.Peek(0) == 0x3e4;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s12, gas - 1)
      else
        ExecuteFromCFGNode_s57(s12, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 46
    * Starting at 0x2f2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Swap3(s10);
      var s12 := Swap2(s11);
      var s13 := Dup4(s12);
      var s14 := Swap1(s13);
      var s15 := Sub(s14);
      var s16 := Push2(s15, 0x0126);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s17, gas - 1)
      else
        ExecuteFromCFGNode_s58(s17, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 47
    * Starting at 0x308
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x308 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0315);
      assert s1.Peek(0) == 0x315;
      var s2 := Swap1(s1);
      var s3 := Dup3(s2);
      var s4 := SLoad(s3);
      var s5 := And(s4);
      var s6 := Caller(s5);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x03e7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s9, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 56
    * Starting at 0x3e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x315

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x315;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x03ee);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s4, gas - 1)
      else
        ExecuteFromCFGNode_s60(s4, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 57
    * Starting at 0x3ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x315

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s1, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 48
    * Starting at 0x315
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x315 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x03d4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s5, gas - 1)
      else
        ExecuteFromCFGNode_s62(s5, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 49
    * Starting at 0x31c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x02);
      var s5 := Dup6(s4);
      var s6 := MStore(s5);
      var s7 := Push2(s6, 0xffff);
      var s8 := Swap3(s7);
      var s9 := Dup4(s8);
      var s10 := Dup6(s9);
      var s11 := Dup4(s10);
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := And(s13);
      var s15 := Push2(s14, 0x03bd);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s16, gas - 1)
      else
        ExecuteFromCFGNode_s63(s16, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 50
    * Starting at 0x331
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      var s2 := Dup5(s1);
      var s3 := Dup7(s2);
      var s4 := Swap3(s3);
      var s5 := Push32(s4, 0xa226db3f664042183ee0281230bba26cbf7b5057e50aee7f25a175ff45ce4d7f);
      var s6 := Swap5(s5);
      var s7 := Push1(s6, 0x05);
      var s8 := SLoad(s7);
      var s9 := Dup8(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Dup2(s10);
      var s12 := Dup4(s11);
      var s13 := And(s12);
      var s14 := Add(s13);
      var s15 := And(s14);
      var s16 := Dup1(s15);
      var s17 := Push2(s16, 0xffff);
      var s18 := Not(s17);
      var s19 := Dup1(s18);
      var s20 := Swap4(s19);
      var s21 := And(s20);
      var s22 := Or(s21);
      var s23 := Push1(s22, 0x05);
      var s24 := SStore(s23);
      var s25 := Dup6(s24);
      var s26 := Dup5(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x02);
      var s29 := Dup8(s28);
      var s30 := MStore(s29);
      var s31 := Dup5(s30);
      var s32 := Dup5(s31);
      var s33 := Keccak256(s32);
      var s34 := Swap2(s33);
      var s35 := Dup3(s34);
      var s36 := SLoad(s35);
      var s37 := And(s36);
      var s38 := Or(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Dup7(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s64(s41, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 51
    * Starting at 0x380
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x380 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x05);
      var s2 := SLoad(s1);
      var s3 := And(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x03);
      var s7 := Dup6(s6);
      var s8 := MStore(s7);
      var s9 := Dup3(s8);
      var s10 := Dup3(s9);
      var s11 := Keccak256(s10);
      var s12 := Dup5(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Dup1(s13);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Not(s17);
      var s19 := Dup3(s18);
      var s20 := SLoad(s19);
      var s21 := And(s20);
      var s22 := Or(s21);
      var s23 := Swap1(s22);
      var s24 := SStore(s23);
      var s25 := Dup4(s24);
      var s26 := Dup3(s25);
      var s27 := MStore(s26);
      var s28 := Dup5(s27);
      var s29 := MStore(s28);
      var s30 := Keccak256(s29);
      var s31 := Push1(s30, 0x01);
      var s32 := Push1(s31, 0xff);
      var s33 := Not(s32);
      var s34 := Dup3(s33);
      var s35 := SLoad(s34);
      var s36 := And(s35);
      var s37 := Or(s36);
      var s38 := Swap1(s37);
      var s39 := SStore(s38);
      var s40 := Dup5(s39);
      var s41 := MLoad(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s65(s41, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 52
    * Starting at 0x3af
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Log1(s3);
      var s5 := Push1(s4, 0x05);
      var s6 := SLoad(s5);
      var s7 := And(s6);
      var s8 := Swap1(s7);
      var s9 := MLoad(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      var s12 := MStore(s11);
      var s13 := Return(s12);
      // Segment is terminal (Revert, Stop or Return)
      s13
  }

  /** Node 66
    * Segment Id for this node is: 53
    * Starting at 0x3bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup5(s1);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0xfa4b50ed);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      var s12 := Dup4(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Swap1(s15);
      var s17 := Revert(s16);
      // Segment is terminal (Revert, Stop or Return)
      s17
  }

  /** Node 67
    * Segment Id for this node is: 54
    * Starting at 0x3d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x49431df5);
      var s5 := Push1(s4, 0xe1);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Dup4(s8);
      var s10 := Swap1(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 68
    * Segment Id for this node is: 58
    * Starting at 0x3ee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x315

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x315;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(4) == 0x315;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x0c);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 12, 0x15539055551213d492569151);
      var s20 := Push1(s19, 0xa2);
      var s21 := Shl(s20);
      assert s21.Peek(2) == 0x315;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Swap1(s26);
      var s28 := Revert(s27);
      // Segment is terminal (Revert, Stop or Return)
      s28
  }

  /** Node 69
    * Segment Id for this node is: 55
    * Starting at 0x3e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }
}
