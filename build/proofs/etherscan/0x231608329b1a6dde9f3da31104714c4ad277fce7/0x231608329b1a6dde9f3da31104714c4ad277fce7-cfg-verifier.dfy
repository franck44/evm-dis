include "../../../../src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module  {:disableNonlinearArithmetic} EVMProofObject {

  import opened AbstractSemantics
  import opened AbstractState

  /** Node 0
    * Segment Id for this node is: 0
    * Starting at 0x0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
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
      var s3 := MStore(s2);
      var s4 := CallValue(s3);
      var s5 := Dup1(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x000f);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s2(s8, gas - 1)
      else
        ExecuteFromCFGNode_s1(s8, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0xc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0xf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x04);
      var s4 := CallDataSize(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x004a);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s224(s7, gas - 1)
      else
        ExecuteFromCFGNode_s3(s7, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x19
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shr(s3);
      var s5 := Dup1(s4);
      var s6 := Push4(s5, 0x35735cc2);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x004e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s9, gas - 1)
      else
        ExecuteFromCFGNode_s4(s9, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x29
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa87430ba);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0063);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x34
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xce83e369);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00c5);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf851a440);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00d8);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x4a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 8
    * Segment Id for this node is: 17
    * Starting at 0xd8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x00eb);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(1) == 0xeb;
      var s12 := Dup2(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s13, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 18
    * Starting at 0xeb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Swap1(s8);
      var s10 := Swap2(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0xeb;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x00bc);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s17, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 14
    * Starting at 0xbc
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 11
    * Segment Id for this node is: 15
    * Starting at 0xc5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0061);
      var s3 := Push2(s2, 0x00d3);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0552);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s7, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 87
    * Starting at 0x552
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x552 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xd3

    requires s0.stack[3] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3;
      assert s1.Peek(3) == 0x61;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0564);
      assert s11.Peek(0) == 0x564;
      assert s11.Peek(7) == 0xd3;
      assert s11.Peek(8) == 0x61;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s12, gas - 1)
      else
        ExecuteFromCFGNode_s13(s12, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 88
    * Starting at 0x561
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x561 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xd3

    requires s0.stack[6] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0xd3;
      assert s1.Peek(7) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 14
    * Segment Id for this node is: 89
    * Starting at 0x564
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x564 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xd3

    requires s0.stack[6] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd3;
      assert s1.Peek(6) == 0x61;
      var s2 := Dup4(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup5(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(5) == 0xd3;
      assert s11.Peek(6) == 0x61;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup5(s12);
      var s14 := Add(s13);
      var s15 := CallDataLoad(s14);
      var s16 := Push8(s15, 0xffffffffffffffff);
      var s17 := Dup2(s16);
      var s18 := Gt(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0588);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s21, gas - 1)
      else
        ExecuteFromCFGNode_s15(s21, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 90
    * Starting at 0x585
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x585 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xd3

    requires s0.stack[7] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0xd3;
      assert s1.Peek(8) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 16
    * Segment Id for this node is: 91
    * Starting at 0x588
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x588 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xd3

    requires s0.stack[7] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xd3;
      assert s1.Peek(7) == 0x61;
      var s2 := Push2(s1, 0x0594);
      var s3 := Dup7(s2);
      var s4 := Dup3(s3);
      var s5 := Dup8(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x03e9);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s8, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 56
    * Starting at 0x3e9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x594

    requires s0.stack[9] == 0xd3

    requires s0.stack[10] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x594;
      assert s1.Peek(9) == 0xd3;
      assert s1.Peek(10) == 0x61;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x03fa);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s10, gas - 1)
      else
        ExecuteFromCFGNode_s18(s10, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 57
    * Starting at 0x3f7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x594

    requires s0.stack[11] == 0xd3

    requires s0.stack[12] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x594;
      assert s1.Peek(12) == 0xd3;
      assert s1.Peek(13) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 19
    * Segment Id for this node is: 58
    * Starting at 0x3fa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x594

    requires s0.stack[11] == 0xd3

    requires s0.stack[12] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x594;
      assert s1.Peek(11) == 0xd3;
      assert s1.Peek(12) == 0x61;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push8(s4, 0xffffffffffffffff);
      var s6 := Dup1(s5);
      var s7 := Dup4(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0417);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s11, gas - 1)
      else
        ExecuteFromCFGNode_s20(s11, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 59
    * Starting at 0x410
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x410 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[7] == 0x594

    requires s0.stack[14] == 0xd3

    requires s0.stack[15] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0417);
      assert s1.Peek(0) == 0x417;
      assert s1.Peek(8) == 0x594;
      assert s1.Peek(15) == 0xd3;
      assert s1.Peek(16) == 0x61;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s3, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x417

    requires s0.stack[8] == 0x594

    requires s0.stack[15] == 0xd3

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x417;
      assert s1.Peek(8) == 0x594;
      assert s1.Peek(15) == 0xd3;
      assert s1.Peek(16) == 0x61;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x417;
      assert s11.Peek(10) == 0x594;
      assert s11.Peek(17) == 0xd3;
      assert s11.Peek(18) == 0x61;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 22
    * Segment Id for this node is: 60
    * Starting at 0x417
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x417 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[7] == 0x594

    requires s0.stack[14] == 0xd3

    requires s0.stack[15] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x594;
      assert s1.Peek(14) == 0xd3;
      assert s1.Peek(15) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Push2(s4, 0x0426);
      var s6 := Dup4(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x03b8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s10, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 53
    * Starting at 0x3b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x426

    requires s0.stack[10] == 0x594

    requires s0.stack[17] == 0xd3

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x426;
      assert s1.Peek(10) == 0x594;
      assert s1.Peek(17) == 0xd3;
      assert s1.Peek(18) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x426;
      assert s11.Peek(12) == 0x594;
      assert s11.Peek(19) == 0xd3;
      assert s11.Peek(20) == 0x61;
      var s12 := Push8(s11, 0xffffffffffffffff);
      var s13 := Dup2(s12);
      var s14 := Gt(s13);
      var s15 := Dup3(s14);
      var s16 := Dup3(s15);
      var s17 := Lt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x03e1);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s26(s21, gas - 1)
      else
        ExecuteFromCFGNode_s24(s21, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 54
    * Starting at 0x3da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x426

    requires s0.stack[12] == 0x594

    requires s0.stack[19] == 0xd3

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03e1);
      assert s1.Peek(0) == 0x3e1;
      assert s1.Peek(4) == 0x426;
      assert s1.Peek(13) == 0x594;
      assert s1.Peek(20) == 0xd3;
      assert s1.Peek(21) == 0x61;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s3, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x3e1

    requires s0.stack[4] == 0x426

    requires s0.stack[13] == 0x594

    requires s0.stack[20] == 0xd3

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3e1;
      assert s1.Peek(4) == 0x426;
      assert s1.Peek(13) == 0x594;
      assert s1.Peek(20) == 0xd3;
      assert s1.Peek(21) == 0x61;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x3e1;
      assert s11.Peek(6) == 0x426;
      assert s11.Peek(15) == 0x594;
      assert s11.Peek(22) == 0xd3;
      assert s11.Peek(23) == 0x61;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 26
    * Segment Id for this node is: 55
    * Starting at 0x3e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x426

    requires s0.stack[12] == 0x594

    requires s0.stack[19] == 0xd3

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x426;
      assert s1.Peek(12) == 0x594;
      assert s1.Peek(19) == 0xd3;
      assert s1.Peek(20) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s7, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 61
    * Starting at 0x426
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x426 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[9] == 0x594

    requires s0.stack[16] == 0xd3

    requires s0.stack[17] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x594;
      assert s1.Peek(16) == 0xd3;
      assert s1.Peek(17) == 0x61;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := MStore(s3);
      var s5 := Dup7(s4);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Swap4(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(10) == 0x594;
      assert s11.Peek(17) == 0xd3;
      assert s11.Peek(18) == 0x61;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup10(s14);
      var s16 := Dup7(s15);
      var s17 := Gt(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x043f);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s20, gas - 1)
      else
        ExecuteFromCFGNode_s28(s20, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 62
    * Starting at 0x43c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x594

    requires s0.stack[17] == 0xd3

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(11) == 0x594;
      assert s1.Peek(18) == 0xd3;
      assert s1.Peek(19) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 29
    * Segment Id for this node is: 63
    * Starting at 0x43f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x594

    requires s0.stack[17] == 0xd3

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x594;
      assert s1.Peek(17) == 0xd3;
      assert s1.Peek(18) == 0x61;
      var s2 := Dup5(s1);
      var s3 := Dup10(s2);
      var s4 := Add(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s30(s6, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 64
    * Starting at 0x445
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x445 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x594

    requires s0.stack[17] == 0xd3

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x594;
      assert s1.Peek(17) == 0xd3;
      assert s1.Peek(18) == 0x61;
      var s2 := Dup6(s1);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04c8);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s46(s7, gas - 1)
      else
        ExecuteFromCFGNode_s31(s7, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 65
    * Starting at 0x44e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x594

    requires s0.stack[17] == 0xd3

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(11) == 0x594;
      assert s1.Peek(18) == 0xd3;
      assert s1.Peek(19) == 0x61;
      var s2 := CallDataLoad(s1);
      var s3 := Dup5(s2);
      var s4 := Dup2(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x045b);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s8, gas - 1)
      else
        ExecuteFromCFGNode_s32(s8, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 66
    * Starting at 0x458
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x458 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x594

    requires s0.stack[18] == 0xd3

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(12) == 0x594;
      assert s1.Peek(19) == 0xd3;
      assert s1.Peek(20) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 33
    * Segment Id for this node is: 67
    * Starting at 0x45b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x594

    requires s0.stack[18] == 0xd3

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x594;
      assert s1.Peek(18) == 0xd3;
      assert s1.Peek(19) == 0x61;
      var s2 := Dup10(s1);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x3f);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := Dup12(s6);
      var s8 := SGt(s7);
      var s9 := Push2(s8, 0x046b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s10, gas - 1)
      else
        ExecuteFromCFGNode_s34(s10, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 68
    * Starting at 0x468
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x468 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x594

    requires s0.stack[18] == 0xd3

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(12) == 0x594;
      assert s1.Peek(19) == 0xd3;
      assert s1.Peek(20) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 35
    * Segment Id for this node is: 69
    * Starting at 0x46b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x594

    requires s0.stack[18] == 0xd3

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x594;
      assert s1.Peek(18) == 0xd3;
      assert s1.Peek(19) == 0x61;
      var s2 := Dup6(s1);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Gt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0481);
      assert s11.Peek(0) == 0x481;
      assert s11.Peek(15) == 0x594;
      assert s11.Peek(22) == 0xd3;
      assert s11.Peek(23) == 0x61;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s12, gas - 1)
      else
        ExecuteFromCFGNode_s36(s12, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 70
    * Starting at 0x47a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[13] == 0x594

    requires s0.stack[20] == 0xd3

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0481);
      assert s1.Peek(0) == 0x481;
      assert s1.Peek(14) == 0x594;
      assert s1.Peek(21) == 0xd3;
      assert s1.Peek(22) == 0x61;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s3, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x481

    requires s0.stack[14] == 0x594

    requires s0.stack[21] == 0xd3

    requires s0.stack[22] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x481;
      assert s1.Peek(14) == 0x594;
      assert s1.Peek(21) == 0xd3;
      assert s1.Peek(22) == 0x61;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x481;
      assert s11.Peek(16) == 0x594;
      assert s11.Peek(23) == 0xd3;
      assert s11.Peek(24) == 0x61;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 38
    * Segment Id for this node is: 71
    * Starting at 0x481
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x481 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[13] == 0x594

    requires s0.stack[20] == 0xd3

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x594;
      assert s1.Peek(20) == 0xd3;
      assert s1.Peek(21) == 0x61;
      var s2 := Push2(s1, 0x0492);
      var s3 := Dup3(s2);
      var s4 := Dup12(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Not(s6);
      var s8 := And(s7);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x03b8);
      assert s11.Peek(0) == 0x3b8;
      assert s11.Peek(2) == 0x492;
      assert s11.Peek(16) == 0x594;
      assert s11.Peek(23) == 0xd3;
      assert s11.Peek(24) == 0x61;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s12, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 53
    * Starting at 0x3b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[1] == 0x492

    requires s0.stack[15] == 0x594

    requires s0.stack[22] == 0xd3

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x492;
      assert s1.Peek(15) == 0x594;
      assert s1.Peek(22) == 0xd3;
      assert s1.Peek(23) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x492;
      assert s11.Peek(17) == 0x594;
      assert s11.Peek(24) == 0xd3;
      assert s11.Peek(25) == 0x61;
      var s12 := Push8(s11, 0xffffffffffffffff);
      var s13 := Dup2(s12);
      var s14 := Gt(s13);
      var s15 := Dup3(s14);
      var s16 := Dup3(s15);
      var s17 := Lt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x03e1);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s21, gas - 1)
      else
        ExecuteFromCFGNode_s40(s21, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 54
    * Starting at 0x3da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0x492

    requires s0.stack[17] == 0x594

    requires s0.stack[24] == 0xd3

    requires s0.stack[25] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03e1);
      assert s1.Peek(0) == 0x3e1;
      assert s1.Peek(4) == 0x492;
      assert s1.Peek(18) == 0x594;
      assert s1.Peek(25) == 0xd3;
      assert s1.Peek(26) == 0x61;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s3, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[0] == 0x3e1

    requires s0.stack[4] == 0x492

    requires s0.stack[18] == 0x594

    requires s0.stack[25] == 0xd3

    requires s0.stack[26] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3e1;
      assert s1.Peek(4) == 0x492;
      assert s1.Peek(18) == 0x594;
      assert s1.Peek(25) == 0xd3;
      assert s1.Peek(26) == 0x61;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x3e1;
      assert s11.Peek(6) == 0x492;
      assert s11.Peek(20) == 0x594;
      assert s11.Peek(27) == 0xd3;
      assert s11.Peek(28) == 0x61;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 42
    * Segment Id for this node is: 55
    * Starting at 0x3e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0x492

    requires s0.stack[17] == 0x594

    requires s0.stack[24] == 0xd3

    requires s0.stack[25] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x492;
      assert s1.Peek(17) == 0x594;
      assert s1.Peek(24) == 0xd3;
      assert s1.Peek(25) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s7, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 72
    * Starting at 0x492
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[14] == 0x594

    requires s0.stack[21] == 0xd3

    requires s0.stack[22] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x594;
      assert s1.Peek(21) == 0xd3;
      assert s1.Peek(22) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Dup14(s4);
      var s6 := Dup3(s5);
      var s7 := Dup5(s6);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Add(s9);
      var s11 := Gt(s10);
      assert s11.Peek(15) == 0x594;
      assert s11.Peek(22) == 0xd3;
      assert s11.Peek(23) == 0x61;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x04a5);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s14, gas - 1)
      else
        ExecuteFromCFGNode_s44(s14, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 73
    * Starting at 0x4a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[14] == 0x594

    requires s0.stack[21] == 0xd3

    requires s0.stack[22] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(15) == 0x594;
      assert s1.Peek(22) == 0xd3;
      assert s1.Peek(23) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 45
    * Segment Id for this node is: 74
    * Starting at 0x4a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[14] == 0x594

    requires s0.stack[21] == 0xd3

    requires s0.stack[22] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x594;
      assert s1.Peek(21) == 0xd3;
      assert s1.Peek(22) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Dup6(s3);
      var s5 := Add(s4);
      var s6 := Dup11(s5);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push0(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(15) == 0x594;
      assert s11.Peek(22) == 0xd3;
      assert s11.Peek(23) == 0x61;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Dup10(s13);
      var s15 := Add(s14);
      var s16 := Swap3(s15);
      var s17 := Swap1(s16);
      var s18 := Swap3(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(13) == 0x594;
      assert s21.Peek(20) == 0xd3;
      assert s21.Peek(21) == 0x61;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Swap2(s23);
      var s25 := Dup5(s24);
      var s26 := Add(s25);
      var s27 := Swap2(s26);
      var s28 := Swap1(s27);
      var s29 := Dup5(s28);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(10) == 0x594;
      assert s31.Peek(17) == 0xd3;
      assert s31.Peek(18) == 0x61;
      var s32 := Push2(s31, 0x0445);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s33, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 75
    * Starting at 0x4c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -10
    * Net Capacity Effect: +10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x594

    requires s0.stack[17] == 0xd3

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x594;
      assert s1.Peek(17) == 0xd3;
      assert s1.Peek(18) == 0x61;
      var s2 := Swap(s1, 10);
      var s3 := Swap(s2, 9);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x594;
      assert s11.Peek(9) == 0xd3;
      assert s11.Peek(10) == 0x61;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s13, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 92
    * Starting at 0x594
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x594 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0xd3

    requires s0.stack[8] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xd3;
      assert s1.Peek(8) == 0x61;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s10, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 16
    * Starting at 0xd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x61;
      var s2 := Push2(s1, 0x020c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s3, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 27
    * Starting at 0x20c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x61;
      var s2 := Caller(s1);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Swap1(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x61;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := SLoad(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0xa0);
      var s18 := Shl(s17);
      var s19 := Sub(s18);
      var s20 := And(s19);
      var s21 := Push2(s20, 0x0268);
      assert s21.Peek(0) == 0x268;
      assert s21.Peek(5) == 0x61;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s22, gas - 1)
      else
        ExecuteFromCFGNode_s50(s22, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 28
    * Starting at 0x229
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x229 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x61;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x61;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x15);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 21, 0x2737ba1030903932b3b4b9ba32b932b2103ab9b2b9);
      var s19 := Push1(s18, 0x59);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x61;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x014a);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s28, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 21
    * Starting at 0x14a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Revert(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 52
    * Segment Id for this node is: 29
    * Starting at 0x268
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x268 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x61;
      var s2 := Caller(s1);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(6) == 0x61;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := Keccak256(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup6(s17);
      var s19 := Swap1(s18);
      var s20 := SStore(s19);
      var s21 := Push1(s20, 0x02);
      assert s21.Peek(6) == 0x61;
      var s22 := Dup2(s21);
      var s23 := Add(s22);
      var s24 := Dup5(s23);
      var s25 := Swap1(s24);
      var s26 := SStore(s25);
      var s27 := Dup3(s26);
      var s28 := MLoad(s27);
      var s29 := Swap1(s28);
      var s30 := Swap2(s29);
      var s31 := Push2(s30, 0x029a);
      assert s31.Peek(0) == 0x29a;
      assert s31.Peek(7) == 0x61;
      var s32 := Swap2(s31);
      var s33 := Push1(s32, 0x03);
      var s34 := Dup5(s33);
      var s35 := Add(s34);
      var s36 := Swap2(s35);
      var s37 := Dup6(s36);
      var s38 := Add(s37);
      var s39 := Swap1(s38);
      var s40 := Push2(s39, 0x02cb);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s41, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 31
    * Starting at 0x2cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x29a

    requires s0.stack[8] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x29a;
      assert s1.Peek(8) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := SStore(s6);
      var s8 := Swap1(s7);
      var s9 := Push0(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(5) == 0x29a;
      assert s11.Peek(10) == 0x61;
      var s12 := Push0(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Swap3(s16);
      var s18 := Dup3(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x030f);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s21, gas - 1)
      else
        ExecuteFromCFGNode_s54(s21, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 32
    * Starting at 0x2e3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x29a

    requires s0.stack[10] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0x29a;
      assert s1.Peek(10) == 0x61;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s55(s5, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 33
    * Starting at 0x2e9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x29a

    requires s0.stack[10] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x29a;
      assert s1.Peek(10) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x030f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s7, gas - 1)
      else
        ExecuteFromCFGNode_s56(s7, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 34
    * Starting at 0x2f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x29a

    requires s0.stack[10] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(6) == 0x29a;
      assert s1.Peek(11) == 0x61;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x02ff);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := Push2(s7, 0x0622);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s9, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 106
    * Starting at 0x622
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x622 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x2ff

    requires s0.stack[9] == 0x29a

    requires s0.stack[14] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2ff;
      assert s1.Peek(9) == 0x29a;
      assert s1.Peek(14) == 0x61;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x063c);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s9, gas - 1)
      else
        ExecuteFromCFGNode_s58(s9, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 107
    * Starting at 0x635
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x635 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x2ff

    requires s0.stack[10] == 0x29a

    requires s0.stack[15] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x063c);
      assert s1.Peek(0) == 0x63c;
      assert s1.Peek(4) == 0x2ff;
      assert s1.Peek(11) == 0x29a;
      assert s1.Peek(16) == 0x61;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s3, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x63c

    requires s0.stack[4] == 0x2ff

    requires s0.stack[11] == 0x29a

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x63c;
      assert s1.Peek(4) == 0x2ff;
      assert s1.Peek(11) == 0x29a;
      assert s1.Peek(16) == 0x61;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x63c;
      assert s11.Peek(6) == 0x2ff;
      assert s11.Peek(13) == 0x29a;
      assert s11.Peek(18) == 0x61;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 60
    * Segment Id for this node is: 108
    * Starting at 0x63c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x2ff

    requires s0.stack[10] == 0x29a

    requires s0.stack[15] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ff;
      assert s1.Peek(10) == 0x29a;
      assert s1.Peek(15) == 0x61;
      var s2 := Push2(s1, 0x0650);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x064a);
      var s5 := Dup5(s4);
      var s6 := SLoad(s5);
      var s7 := Push2(s6, 0x059e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s8, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 93
    * Starting at 0x59e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x64a

    requires s0.stack[3] == 0x650

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x29a

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64a;
      assert s1.Peek(3) == 0x650;
      assert s1.Peek(7) == 0x2ff;
      assert s1.Peek(14) == 0x29a;
      assert s1.Peek(19) == 0x61;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x05b2);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s11, gas - 1)
      else
        ExecuteFromCFGNode_s62(s11, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 94
    * Starting at 0x5ac
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x64a

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x64a;
      assert s1.Peek(6) == 0x650;
      assert s1.Peek(10) == 0x2ff;
      assert s1.Peek(17) == 0x29a;
      assert s1.Peek(22) == 0x61;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s63(s5, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 95
    * Starting at 0x5b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x64a

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x64a;
      assert s1.Peek(5) == 0x650;
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x29a;
      assert s1.Peek(21) == 0x61;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x05d0);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s8, gas - 1)
      else
        ExecuteFromCFGNode_s64(s8, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 96
    * Starting at 0x5bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x64a

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x64a;
      assert s1.Peek(6) == 0x650;
      assert s1.Peek(10) == 0x2ff;
      assert s1.Peek(17) == 0x29a;
      assert s1.Peek(22) == 0x61;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 65
    * Segment Id for this node is: 97
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x64a

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x64a;
      assert s1.Peek(5) == 0x650;
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x29a;
      assert s1.Peek(21) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s6, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 109
    * Starting at 0x64a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x650

    requires s0.stack[6] == 0x2ff

    requires s0.stack[13] == 0x29a

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x650;
      assert s1.Peek(6) == 0x2ff;
      assert s1.Peek(13) == 0x29a;
      assert s1.Peek(18) == 0x61;
      var s2 := Dup5(s1);
      var s3 := Push2(s2, 0x05d6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s4, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 98
    * Starting at 0x5d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x650

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x29a

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x650;
      assert s1.Peek(7) == 0x2ff;
      assert s1.Peek(14) == 0x29a;
      assert s1.Peek(19) == 0x61;
      var s2 := Push1(s1, 0x1f);
      var s3 := Dup3(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x061d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s7, gas - 1)
      else
        ExecuteFromCFGNode_s68(s7, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 99
    * Starting at 0x5e0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x650

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x29a

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x650;
      assert s1.Peek(8) == 0x2ff;
      assert s1.Peek(15) == 0x29a;
      assert s1.Peek(20) == 0x61;
      var s2 := Push0(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push0(s4);
      var s6 := Keccak256(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x05);
      var s11 := Shr(s10);
      assert s11.Peek(5) == 0x650;
      assert s11.Peek(9) == 0x2ff;
      assert s11.Peek(16) == 0x29a;
      assert s11.Peek(21) == 0x61;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup6(s14);
      var s16 := Lt(s15);
      var s17 := IsZero(s16);
      var s18 := Push2(s17, 0x05fb);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s19, gas - 1)
      else
        ExecuteFromCFGNode_s69(s19, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 100
    * Starting at 0x5f9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x650;
      assert s1.Peek(8) == 0x2ff;
      assert s1.Peek(15) == 0x29a;
      assert s1.Peek(20) == 0x61;
      var s2 := Dup1(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s70(s2, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 101
    * Starting at 0x5fb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x650;
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x29a;
      assert s1.Peek(21) == 0x61;
      var s2 := Push1(s1, 0x1f);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x05);
      var s6 := Shr(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Pop(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s71(s10, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 102
    * Starting at 0x607
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x607 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x650;
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x29a;
      assert s1.Peek(21) == 0x61;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x061a);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s7, gas - 1)
      else
        ExecuteFromCFGNode_s72(s7, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 103
    * Starting at 0x610
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x610 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x650;
      assert s1.Peek(10) == 0x2ff;
      assert s1.Peek(17) == 0x29a;
      assert s1.Peek(22) == 0x61;
      var s2 := Dup2(s1);
      var s3 := SStore(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Add(s4);
      var s6 := Push2(s5, 0x0607);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s7, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 104
    * Starting at 0x61a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x650;
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x29a;
      assert s1.Peek(21) == 0x61;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s74(s3, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 105
    * Starting at 0x61d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x650

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x29a

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x650;
      assert s1.Peek(7) == 0x2ff;
      assert s1.Peek(14) == 0x29a;
      assert s1.Peek(19) == 0x61;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s5, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 110
    * Starting at 0x650
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x650 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x2ff

    requires s0.stack[10] == 0x29a

    requires s0.stack[15] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ff;
      assert s1.Peek(10) == 0x29a;
      assert s1.Peek(15) == 0x61;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Gt(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Dup2(s7);
      var s9 := Eq(s8);
      var s10 := Push2(s9, 0x0683);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s11, gas - 1)
      else
        ExecuteFromCFGNode_s76(s11, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 111
    * Starting at 0x660
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x660 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x2ff

    requires s0.stack[13] == 0x29a

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x2ff;
      assert s1.Peek(14) == 0x29a;
      assert s1.Peek(19) == 0x61;
      var s2 := Dup5(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x066c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s5, gas - 1)
      else
        ExecuteFromCFGNode_s77(s5, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 112
    * Starting at 0x667
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x667 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x29a

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(6) == 0x2ff;
      assert s1.Peek(13) == 0x29a;
      assert s1.Peek(18) == 0x61;
      var s2 := Dup6(s1);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s78(s5, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 113
    * Starting at 0x66c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x29a

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x2ff;
      assert s1.Peek(14) == 0x29a;
      assert s1.Peek(19) == 0x61;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Push1(s3, 0x03);
      var s5 := Dup7(s4);
      var s6 := Swap1(s5);
      var s7 := Shl(s6);
      var s8 := Shr(s7);
      var s9 := Not(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(8) == 0x2ff;
      assert s11.Peek(15) == 0x29a;
      assert s11.Peek(20) == 0x61;
      var s12 := Dup6(s11);
      var s13 := Swap1(s12);
      var s14 := Shl(s13);
      var s15 := Or(s14);
      var s16 := Dup6(s15);
      var s17 := SStore(s16);
      var s18 := Push2(s17, 0x06da);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s19, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 120
    * Starting at 0x6da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x2ff

    requires s0.stack[13] == 0x29a

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2ff;
      assert s1.Peek(13) == 0x29a;
      assert s1.Peek(18) == 0x61;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s8, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 35
    * Starting at 0x2ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x29a

    requires s0.stack[11] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x29a;
      assert s1.Peek(11) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x02e9);
      assert s11.Peek(0) == 0x2e9;
      assert s11.Peek(6) == 0x29a;
      assert s11.Peek(11) == 0x61;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s12, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 114
    * Starting at 0x683
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x683 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x2ff

    requires s0.stack[13] == 0x29a

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2ff;
      assert s1.Peek(13) == 0x29a;
      assert s1.Peek(18) == 0x61;
      var s2 := Push0(s1);
      var s3 := Dup6(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Keccak256(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Not(s9);
      var s11 := Dup7(s10);
      assert s11.Peek(10) == 0x2ff;
      assert s11.Peek(17) == 0x29a;
      assert s11.Peek(22) == 0x61;
      var s12 := And(s11);
      var s13 := Swap2(s12);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s82(s13, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 115
    * Starting at 0x692
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x692 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x29a;
      assert s1.Peek(21) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x06b1);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s7, gas - 1)
      else
        ExecuteFromCFGNode_s83(s7, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 116
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup9(s0);
      assert s1.Peek(10) == 0x2ff;
      assert s1.Peek(17) == 0x29a;
      assert s1.Peek(22) == 0x61;
      var s2 := Dup7(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup3(s4);
      var s6 := SStore(s5);
      var s7 := Swap5(s6);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := Swap5(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(10) == 0x2ff;
      assert s11.Peek(17) == 0x29a;
      assert s11.Peek(22) == 0x61;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := Add(s13);
      var s15 := Swap1(s14);
      var s16 := Dup5(s15);
      var s17 := Add(s16);
      var s18 := Push2(s17, 0x0692);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s19, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 117
    * Starting at 0x6b1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x29a

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x29a;
      assert s1.Peek(21) == 0x61;
      var s2 := Pop(s1);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x06ce);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s8, gas - 1)
      else
        ExecuteFromCFGNode_s85(s8, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 118
    * Starting at 0x6bb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[8] == 0x2ff

    requires s0.stack[15] == 0x29a

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup8(s0);
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x29a;
      assert s1.Peek(21) == 0x61;
      var s2 := Dup6(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Push0(s4);
      var s6 := Not(s5);
      var s7 := Push1(s6, 0x03);
      var s8 := Dup9(s7);
      var s9 := Swap1(s8);
      var s10 := Shl(s9);
      var s11 := Push1(s10, 0xf8);
      assert s11.Peek(12) == 0x2ff;
      assert s11.Peek(19) == 0x29a;
      assert s11.Peek(24) == 0x61;
      var s12 := And(s11);
      var s13 := Shr(s12);
      var s14 := Not(s13);
      var s15 := And(s14);
      var s16 := Dup2(s15);
      var s17 := SStore(s16);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s86(s17, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 119
    * Starting at 0x6ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[8] == 0x2ff

    requires s0.stack[15] == 0x29a

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x2ff;
      assert s1.Peek(15) == 0x29a;
      assert s1.Peek(20) == 0x61;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Shl(s6);
      var s8 := Add(s7);
      var s9 := Dup6(s8);
      var s10 := SStore(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s79(s10, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 36
    * Starting at 0x30f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x29a

    requires s0.stack[10] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x29a;
      assert s1.Peek(10) == 0x61;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x031b);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x031f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s8, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 38
    * Starting at 0x31f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x31b

    requires s0.stack[4] == 0x29a

    requires s0.stack[9] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31b;
      assert s1.Peek(4) == 0x29a;
      assert s1.Peek(9) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x031b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s7, gas - 1)
      else
        ExecuteFromCFGNode_s89(s7, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 39
    * Starting at 0x328
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x328 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x31b

    requires s0.stack[4] == 0x29a

    requires s0.stack[9] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x31b;
      assert s1.Peek(5) == 0x29a;
      assert s1.Peek(10) == 0x61;
      var s2 := Push2(s1, 0x0332);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x033b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s6, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 41
    * Starting at 0x33b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x332

    requires s0.stack[6] == 0x31b

    requires s0.stack[8] == 0x29a

    requires s0.stack[13] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x332;
      assert s1.Peek(6) == 0x31b;
      assert s1.Peek(8) == 0x29a;
      assert s1.Peek(13) == 0x61;
      var s2 := Pop(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x0347);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x059e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s8, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 93
    * Starting at 0x59e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x347

    requires s0.stack[3] == 0x332

    requires s0.stack[7] == 0x31b

    requires s0.stack[9] == 0x29a

    requires s0.stack[14] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x347;
      assert s1.Peek(3) == 0x332;
      assert s1.Peek(7) == 0x31b;
      assert s1.Peek(9) == 0x29a;
      assert s1.Peek(14) == 0x61;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x05b2);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s11, gas - 1)
      else
        ExecuteFromCFGNode_s92(s11, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 94
    * Starting at 0x5ac
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x347

    requires s0.stack[5] == 0x332

    requires s0.stack[9] == 0x31b

    requires s0.stack[11] == 0x29a

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x347;
      assert s1.Peek(6) == 0x332;
      assert s1.Peek(10) == 0x31b;
      assert s1.Peek(12) == 0x29a;
      assert s1.Peek(17) == 0x61;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s93(s5, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 95
    * Starting at 0x5b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x347

    requires s0.stack[5] == 0x332

    requires s0.stack[9] == 0x31b

    requires s0.stack[11] == 0x29a

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x347;
      assert s1.Peek(5) == 0x332;
      assert s1.Peek(9) == 0x31b;
      assert s1.Peek(11) == 0x29a;
      assert s1.Peek(16) == 0x61;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x05d0);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s8, gas - 1)
      else
        ExecuteFromCFGNode_s94(s8, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 96
    * Starting at 0x5bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x347

    requires s0.stack[5] == 0x332

    requires s0.stack[9] == 0x31b

    requires s0.stack[11] == 0x29a

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x347;
      assert s1.Peek(6) == 0x332;
      assert s1.Peek(10) == 0x31b;
      assert s1.Peek(12) == 0x29a;
      assert s1.Peek(17) == 0x61;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 95
    * Segment Id for this node is: 97
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x347

    requires s0.stack[5] == 0x332

    requires s0.stack[9] == 0x31b

    requires s0.stack[11] == 0x29a

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x347;
      assert s1.Peek(5) == 0x332;
      assert s1.Peek(9) == 0x31b;
      assert s1.Peek(11) == 0x29a;
      assert s1.Peek(16) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s6, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 42
    * Starting at 0x347
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x347 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x332

    requires s0.stack[6] == 0x31b

    requires s0.stack[8] == 0x29a

    requires s0.stack[13] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x332;
      assert s1.Peek(6) == 0x31b;
      assert s1.Peek(8) == 0x29a;
      assert s1.Peek(13) == 0x61;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := SStore(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Lt(s6);
      var s8 := Push2(s7, 0x0356);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s99(s9, gas - 1)
      else
        ExecuteFromCFGNode_s97(s9, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 43
    * Starting at 0x353
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x353 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x332

    requires s0.stack[6] == 0x31b

    requires s0.stack[8] == 0x29a

    requires s0.stack[13] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0x332;
      assert s1.Peek(5) == 0x31b;
      assert s1.Peek(7) == 0x29a;
      assert s1.Peek(12) == 0x61;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s3, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 40
    * Starting at 0x332
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x332 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x31b

    requires s0.stack[5] == 0x29a

    requires s0.stack[10] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x31b;
      assert s1.Peek(5) == 0x29a;
      assert s1.Peek(10) == 0x61;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Add(s3);
      var s5 := Push2(s4, 0x031f);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s6, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 44
    * Starting at 0x356
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x356 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x332

    requires s0.stack[6] == 0x31b

    requires s0.stack[8] == 0x29a

    requires s0.stack[13] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x332;
      assert s1.Peek(6) == 0x31b;
      assert s1.Peek(8) == 0x29a;
      assert s1.Peek(13) == 0x61;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Swap1(s4);
      var s6 := Div(s5);
      var s7 := Swap1(s6);
      var s8 := Push0(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push0(s10);
      assert s11.Peek(3) == 0x332;
      assert s11.Peek(7) == 0x31b;
      assert s11.Peek(9) == 0x29a;
      assert s11.Peek(14) == 0x61;
      var s12 := Keccak256(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Push2(s16, 0x0372);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Push2(s19, 0x0375);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s21, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 46
    * Starting at 0x375
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x375 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x372

    requires s0.stack[3] == 0x332

    requires s0.stack[7] == 0x31b

    requires s0.stack[9] == 0x29a

    requires s0.stack[14] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s101(s1, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 47
    * Starting at 0x376
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x376 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x372

    requires s0.stack[3] == 0x332

    requires s0.stack[7] == 0x31b

    requires s0.stack[9] == 0x29a

    requires s0.stack[14] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x372;
      assert s1.Peek(3) == 0x332;
      assert s1.Peek(7) == 0x31b;
      assert s1.Peek(9) == 0x29a;
      assert s1.Peek(14) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x031b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s7, gas - 1)
      else
        ExecuteFromCFGNode_s102(s7, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 48
    * Starting at 0x37f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x372

    requires s0.stack[3] == 0x332

    requires s0.stack[7] == 0x31b

    requires s0.stack[9] == 0x29a

    requires s0.stack[14] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(4) == 0x332;
      assert s1.Peek(8) == 0x31b;
      assert s1.Peek(10) == 0x29a;
      assert s1.Peek(15) == 0x61;
      var s2 := Dup2(s1);
      var s3 := SStore(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Add(s4);
      var s6 := Push2(s5, 0x0376);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s7, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 37
    * Starting at 0x31b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x372

    requires s0.stack[3] == 0x332

    requires s0.stack[7] == 0x31b

    requires s0.stack[9] == 0x29a

    requires s0.stack[14] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x372;
      assert s1.Peek(3) == 0x332;
      assert s1.Peek(7) == 0x31b;
      assert s1.Peek(9) == 0x29a;
      assert s1.Peek(14) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s4, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 45
    * Starting at 0x372
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x372 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x332

    requires s0.stack[5] == 0x31b

    requires s0.stack[7] == 0x29a

    requires s0.stack[12] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x332;
      assert s1.Peek(5) == 0x31b;
      assert s1.Peek(7) == 0x29a;
      assert s1.Peek(12) == 0x61;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s3, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 37
    * Starting at 0x31b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x31b

    requires s0.stack[4] == 0x29a

    requires s0.stack[9] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31b;
      assert s1.Peek(4) == 0x29a;
      assert s1.Peek(9) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s4, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 37
    * Starting at 0x31b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x29a

    requires s0.stack[7] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x29a;
      assert s1.Peek(7) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s4, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 30
    * Starting at 0x29a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x61;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Caller(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push32(s7, 0xa7dff163671e610b2bf8ca2e049a3f29bd4e483b11bed1545b16d733ff17780b);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x61;
      var s12 := Push2(s11, 0x01fe);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s13, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 26
    * Starting at 0x1fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log1(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x61;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s13, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 10
    * Starting at 0x61
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Stop(s1);
      // Segment is terminal (Revert, Stop or Return)
      s2
  }

  /** Node 110
    * Segment Id for this node is: 11
    * Starting at 0x63
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x009b);
      var s3 := Push2(s2, 0x0071);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0532);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s7, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 83
    * Starting at 0x532
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x532 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x71

    requires s0.stack[3] == 0x9b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x71;
      assert s1.Peek(3) == 0x9b;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0542);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s113(s10, gas - 1)
      else
        ExecuteFromCFGNode_s112(s10, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 84
    * Starting at 0x53f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x71

    requires s0.stack[4] == 0x9b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x71;
      assert s1.Peek(5) == 0x9b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 113
    * Segment Id for this node is: 85
    * Starting at 0x542
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x542 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x71

    requires s0.stack[4] == 0x9b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x71;
      assert s1.Peek(4) == 0x9b;
      var s2 := Push2(s1, 0x054b);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0389);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s5, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 49
    * Starting at 0x389
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x389 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x54b

    requires s0.stack[5] == 0x71

    requires s0.stack[6] == 0x9b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x54b;
      assert s1.Peek(5) == 0x71;
      assert s1.Peek(6) == 0x9b;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x54b;
      assert s11.Peek(8) == 0x71;
      assert s11.Peek(9) == 0x9b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x039f);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s116(s14, gas - 1)
      else
        ExecuteFromCFGNode_s115(s14, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 50
    * Starting at 0x39c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x54b

    requires s0.stack[6] == 0x71

    requires s0.stack[7] == 0x9b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x54b;
      assert s1.Peek(7) == 0x71;
      assert s1.Peek(8) == 0x9b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 116
    * Segment Id for this node is: 51
    * Starting at 0x39f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x54b

    requires s0.stack[6] == 0x71

    requires s0.stack[7] == 0x9b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x54b;
      assert s1.Peek(6) == 0x71;
      assert s1.Peek(7) == 0x9b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s5, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 86
    * Starting at 0x54b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x71

    requires s0.stack[5] == 0x9b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x71;
      assert s1.Peek(5) == 0x9b;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s7, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 12
    * Starting at 0x71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x9b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9b;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup2(s3);
      var s5 := Swap1(s4);
      var s6 := MStore(s5);
      var s7 := Swap1(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x9b;
      var s12 := Keccak256(s11);
      var s13 := Dup1(s12);
      var s14 := SLoad(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := SLoad(s17);
      var s19 := Push1(s18, 0x02);
      var s20 := Swap1(s19);
      var s21 := Swap3(s20);
      assert s21.Peek(4) == 0x9b;
      var s22 := Add(s21);
      var s23 := SLoad(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0xa0);
      var s27 := Shl(s26);
      var s28 := Sub(s27);
      var s29 := Swap1(s28);
      var s30 := Swap2(s29);
      var s31 := And(s30);
      assert s31.Peek(3) == 0x9b;
      var s32 := Swap2(s31);
      var s33 := Swap1(s32);
      var s34 := Dup4(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s35, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 13
    * Starting at 0x9b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x9b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9b;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Swap5(s10);
      assert s11.Peek(6) == 0x9b;
      var s12 := And(s11);
      var s13 := Dup5(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup5(s15);
      var s17 := Add(s16);
      var s18 := Swap3(s17);
      var s19 := Swap1(s18);
      var s20 := Swap3(s19);
      var s21 := MStore(s20);
      assert s21.Peek(3) == 0x9b;
      var s22 := Swap1(s21);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x60);
      var s27 := Add(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s120(s27, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 14
    * Starting at 0xbc
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x9b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 121
    * Segment Id for this node is: 8
    * Starting at 0x4e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0061);
      var s3 := Push2(s2, 0x005c);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x04d5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s7, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 76
    * Starting at 0x4d5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x5c

    requires s0.stack[3] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5c;
      assert s1.Peek(3) == 0x61;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x80);
      var s7 := Dup6(s6);
      var s8 := Dup8(s7);
      var s9 := Sub(s8);
      var s10 := SLt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(7) == 0x5c;
      assert s11.Peek(8) == 0x61;
      var s12 := Push2(s11, 0x04e8);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s124(s13, gas - 1)
      else
        ExecuteFromCFGNode_s123(s13, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 77
    * Starting at 0x4e5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x5c

    requires s0.stack[7] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x5c;
      assert s1.Peek(8) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 124
    * Segment Id for this node is: 78
    * Starting at 0x4e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x5c

    requires s0.stack[7] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x5c;
      assert s1.Peek(7) == 0x61;
      var s2 := Push2(s1, 0x04f1);
      var s3 := Dup6(s2);
      var s4 := Push2(s3, 0x0389);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s5, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 49
    * Starting at 0x389
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x389 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x4f1

    requires s0.stack[8] == 0x5c

    requires s0.stack[9] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4f1;
      assert s1.Peek(8) == 0x5c;
      assert s1.Peek(9) == 0x61;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x4f1;
      assert s11.Peek(11) == 0x5c;
      assert s11.Peek(12) == 0x61;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x039f);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s14, gas - 1)
      else
        ExecuteFromCFGNode_s126(s14, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 50
    * Starting at 0x39c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x4f1

    requires s0.stack[9] == 0x5c

    requires s0.stack[10] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x4f1;
      assert s1.Peek(10) == 0x5c;
      assert s1.Peek(11) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 127
    * Segment Id for this node is: 51
    * Starting at 0x39f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x4f1

    requires s0.stack[9] == 0x5c

    requires s0.stack[10] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4f1;
      assert s1.Peek(9) == 0x5c;
      assert s1.Peek(10) == 0x61;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s5, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 79
    * Starting at 0x4f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x5c

    requires s0.stack[8] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x5c;
      assert s1.Peek(8) == 0x61;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup6(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Swap3(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x5c;
      assert s11.Peek(9) == 0x61;
      var s12 := Add(s11);
      var s13 := CallDataLoad(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Push1(s15, 0x60);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := CallDataLoad(s18);
      var s20 := Push8(s19, 0xffffffffffffffff);
      var s21 := Dup2(s20);
      assert s21.Peek(9) == 0x5c;
      assert s21.Peek(10) == 0x61;
      var s22 := Gt(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x051a);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s25, gas - 1)
      else
        ExecuteFromCFGNode_s129(s25, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 80
    * Starting at 0x517
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x517 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x5c

    requires s0.stack[8] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(8) == 0x5c;
      assert s1.Peek(9) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 130
    * Segment Id for this node is: 81
    * Starting at 0x51a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x5c

    requires s0.stack[8] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x5c;
      assert s1.Peek(8) == 0x61;
      var s2 := Push2(s1, 0x0526);
      var s3 := Dup8(s2);
      var s4 := Dup3(s3);
      var s5 := Dup9(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x03e9);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s8, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 56
    * Starting at 0x3e9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x526

    requires s0.stack[10] == 0x5c

    requires s0.stack[11] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x526;
      assert s1.Peek(10) == 0x5c;
      assert s1.Peek(11) == 0x61;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x03fa);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s10, gas - 1)
      else
        ExecuteFromCFGNode_s132(s10, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 57
    * Starting at 0x3f7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x526

    requires s0.stack[12] == 0x5c

    requires s0.stack[13] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x526;
      assert s1.Peek(13) == 0x5c;
      assert s1.Peek(14) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 133
    * Segment Id for this node is: 58
    * Starting at 0x3fa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x526

    requires s0.stack[12] == 0x5c

    requires s0.stack[13] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x526;
      assert s1.Peek(12) == 0x5c;
      assert s1.Peek(13) == 0x61;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push8(s4, 0xffffffffffffffff);
      var s6 := Dup1(s5);
      var s7 := Dup4(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0417);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s11, gas - 1)
      else
        ExecuteFromCFGNode_s134(s11, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 59
    * Starting at 0x410
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x410 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0x526

    requires s0.stack[15] == 0x5c

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0417);
      assert s1.Peek(0) == 0x417;
      assert s1.Peek(8) == 0x526;
      assert s1.Peek(16) == 0x5c;
      assert s1.Peek(17) == 0x61;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s3, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0x417

    requires s0.stack[8] == 0x526

    requires s0.stack[16] == 0x5c

    requires s0.stack[17] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x417;
      assert s1.Peek(8) == 0x526;
      assert s1.Peek(16) == 0x5c;
      assert s1.Peek(17) == 0x61;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x417;
      assert s11.Peek(10) == 0x526;
      assert s11.Peek(18) == 0x5c;
      assert s11.Peek(19) == 0x61;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 136
    * Segment Id for this node is: 60
    * Starting at 0x417
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x417 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0x526

    requires s0.stack[15] == 0x5c

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x526;
      assert s1.Peek(15) == 0x5c;
      assert s1.Peek(16) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Push2(s4, 0x0426);
      var s6 := Dup4(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x03b8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s10, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 53
    * Starting at 0x3b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x426

    requires s0.stack[10] == 0x526

    requires s0.stack[18] == 0x5c

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x426;
      assert s1.Peek(10) == 0x526;
      assert s1.Peek(18) == 0x5c;
      assert s1.Peek(19) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x426;
      assert s11.Peek(12) == 0x526;
      assert s11.Peek(20) == 0x5c;
      assert s11.Peek(21) == 0x61;
      var s12 := Push8(s11, 0xffffffffffffffff);
      var s13 := Dup2(s12);
      var s14 := Gt(s13);
      var s15 := Dup3(s14);
      var s16 := Dup3(s15);
      var s17 := Lt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x03e1);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s140(s21, gas - 1)
      else
        ExecuteFromCFGNode_s138(s21, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 54
    * Starting at 0x3da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x426

    requires s0.stack[12] == 0x526

    requires s0.stack[20] == 0x5c

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03e1);
      assert s1.Peek(0) == 0x3e1;
      assert s1.Peek(4) == 0x426;
      assert s1.Peek(13) == 0x526;
      assert s1.Peek(21) == 0x5c;
      assert s1.Peek(22) == 0x61;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s3, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x3e1

    requires s0.stack[4] == 0x426

    requires s0.stack[13] == 0x526

    requires s0.stack[21] == 0x5c

    requires s0.stack[22] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3e1;
      assert s1.Peek(4) == 0x426;
      assert s1.Peek(13) == 0x526;
      assert s1.Peek(21) == 0x5c;
      assert s1.Peek(22) == 0x61;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x3e1;
      assert s11.Peek(6) == 0x426;
      assert s11.Peek(15) == 0x526;
      assert s11.Peek(23) == 0x5c;
      assert s11.Peek(24) == 0x61;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 140
    * Segment Id for this node is: 55
    * Starting at 0x3e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x426

    requires s0.stack[12] == 0x526

    requires s0.stack[20] == 0x5c

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x426;
      assert s1.Peek(12) == 0x526;
      assert s1.Peek(20) == 0x5c;
      assert s1.Peek(21) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s7, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 61
    * Starting at 0x426
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x426 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[9] == 0x526

    requires s0.stack[17] == 0x5c

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x526;
      assert s1.Peek(17) == 0x5c;
      assert s1.Peek(18) == 0x61;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := MStore(s3);
      var s5 := Dup7(s4);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Swap4(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(10) == 0x526;
      assert s11.Peek(18) == 0x5c;
      assert s11.Peek(19) == 0x61;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup10(s14);
      var s16 := Dup7(s15);
      var s17 := Gt(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x043f);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s20, gas - 1)
      else
        ExecuteFromCFGNode_s142(s20, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 62
    * Starting at 0x43c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x526

    requires s0.stack[18] == 0x5c

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(11) == 0x526;
      assert s1.Peek(19) == 0x5c;
      assert s1.Peek(20) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 143
    * Segment Id for this node is: 63
    * Starting at 0x43f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x526

    requires s0.stack[18] == 0x5c

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x526;
      assert s1.Peek(18) == 0x5c;
      assert s1.Peek(19) == 0x61;
      var s2 := Dup5(s1);
      var s3 := Dup10(s2);
      var s4 := Add(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s144(s6, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 64
    * Starting at 0x445
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x445 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x526

    requires s0.stack[18] == 0x5c

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x526;
      assert s1.Peek(18) == 0x5c;
      assert s1.Peek(19) == 0x61;
      var s2 := Dup6(s1);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04c8);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s160(s7, gas - 1)
      else
        ExecuteFromCFGNode_s145(s7, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 65
    * Starting at 0x44e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x526

    requires s0.stack[18] == 0x5c

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(11) == 0x526;
      assert s1.Peek(19) == 0x5c;
      assert s1.Peek(20) == 0x61;
      var s2 := CallDataLoad(s1);
      var s3 := Dup5(s2);
      var s4 := Dup2(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x045b);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s147(s8, gas - 1)
      else
        ExecuteFromCFGNode_s146(s8, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 66
    * Starting at 0x458
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x458 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0x526

    requires s0.stack[19] == 0x5c

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(12) == 0x526;
      assert s1.Peek(20) == 0x5c;
      assert s1.Peek(21) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 147
    * Segment Id for this node is: 67
    * Starting at 0x45b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0x526

    requires s0.stack[19] == 0x5c

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x526;
      assert s1.Peek(19) == 0x5c;
      assert s1.Peek(20) == 0x61;
      var s2 := Dup10(s1);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x3f);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := Dup12(s6);
      var s8 := SGt(s7);
      var s9 := Push2(s8, 0x046b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s10, gas - 1)
      else
        ExecuteFromCFGNode_s148(s10, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 68
    * Starting at 0x468
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x468 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0x526

    requires s0.stack[19] == 0x5c

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(12) == 0x526;
      assert s1.Peek(20) == 0x5c;
      assert s1.Peek(21) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 149
    * Segment Id for this node is: 69
    * Starting at 0x46b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0x526

    requires s0.stack[19] == 0x5c

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x526;
      assert s1.Peek(19) == 0x5c;
      assert s1.Peek(20) == 0x61;
      var s2 := Dup6(s1);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Gt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0481);
      assert s11.Peek(0) == 0x481;
      assert s11.Peek(15) == 0x526;
      assert s11.Peek(23) == 0x5c;
      assert s11.Peek(24) == 0x61;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s12, gas - 1)
      else
        ExecuteFromCFGNode_s150(s12, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 70
    * Starting at 0x47a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[13] == 0x526

    requires s0.stack[21] == 0x5c

    requires s0.stack[22] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0481);
      assert s1.Peek(0) == 0x481;
      assert s1.Peek(14) == 0x526;
      assert s1.Peek(22) == 0x5c;
      assert s1.Peek(23) == 0x61;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s3, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[0] == 0x481

    requires s0.stack[14] == 0x526

    requires s0.stack[22] == 0x5c

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x481;
      assert s1.Peek(14) == 0x526;
      assert s1.Peek(22) == 0x5c;
      assert s1.Peek(23) == 0x61;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x481;
      assert s11.Peek(16) == 0x526;
      assert s11.Peek(24) == 0x5c;
      assert s11.Peek(25) == 0x61;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 152
    * Segment Id for this node is: 71
    * Starting at 0x481
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x481 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[13] == 0x526

    requires s0.stack[21] == 0x5c

    requires s0.stack[22] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x526;
      assert s1.Peek(21) == 0x5c;
      assert s1.Peek(22) == 0x61;
      var s2 := Push2(s1, 0x0492);
      var s3 := Dup3(s2);
      var s4 := Dup12(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Not(s6);
      var s8 := And(s7);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x03b8);
      assert s11.Peek(0) == 0x3b8;
      assert s11.Peek(2) == 0x492;
      assert s11.Peek(16) == 0x526;
      assert s11.Peek(24) == 0x5c;
      assert s11.Peek(25) == 0x61;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s12, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 53
    * Starting at 0x3b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0x492

    requires s0.stack[15] == 0x526

    requires s0.stack[23] == 0x5c

    requires s0.stack[24] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x492;
      assert s1.Peek(15) == 0x526;
      assert s1.Peek(23) == 0x5c;
      assert s1.Peek(24) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x492;
      assert s11.Peek(17) == 0x526;
      assert s11.Peek(25) == 0x5c;
      assert s11.Peek(26) == 0x61;
      var s12 := Push8(s11, 0xffffffffffffffff);
      var s13 := Dup2(s12);
      var s14 := Gt(s13);
      var s15 := Dup3(s14);
      var s16 := Dup3(s15);
      var s17 := Lt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x03e1);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s21, gas - 1)
      else
        ExecuteFromCFGNode_s154(s21, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 54
    * Starting at 0x3da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x492

    requires s0.stack[17] == 0x526

    requires s0.stack[25] == 0x5c

    requires s0.stack[26] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03e1);
      assert s1.Peek(0) == 0x3e1;
      assert s1.Peek(4) == 0x492;
      assert s1.Peek(18) == 0x526;
      assert s1.Peek(26) == 0x5c;
      assert s1.Peek(27) == 0x61;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s3, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[0] == 0x3e1

    requires s0.stack[4] == 0x492

    requires s0.stack[18] == 0x526

    requires s0.stack[26] == 0x5c

    requires s0.stack[27] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3e1;
      assert s1.Peek(4) == 0x492;
      assert s1.Peek(18) == 0x526;
      assert s1.Peek(26) == 0x5c;
      assert s1.Peek(27) == 0x61;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x3e1;
      assert s11.Peek(6) == 0x492;
      assert s11.Peek(20) == 0x526;
      assert s11.Peek(28) == 0x5c;
      assert s11.Peek(29) == 0x61;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 156
    * Segment Id for this node is: 55
    * Starting at 0x3e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x492

    requires s0.stack[17] == 0x526

    requires s0.stack[25] == 0x5c

    requires s0.stack[26] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x492;
      assert s1.Peek(17) == 0x526;
      assert s1.Peek(25) == 0x5c;
      assert s1.Peek(26) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s7, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 72
    * Starting at 0x492
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[14] == 0x526

    requires s0.stack[22] == 0x5c

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x526;
      assert s1.Peek(22) == 0x5c;
      assert s1.Peek(23) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Dup14(s4);
      var s6 := Dup3(s5);
      var s7 := Dup5(s6);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Add(s9);
      var s11 := Gt(s10);
      assert s11.Peek(15) == 0x526;
      assert s11.Peek(23) == 0x5c;
      assert s11.Peek(24) == 0x61;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x04a5);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s14, gas - 1)
      else
        ExecuteFromCFGNode_s158(s14, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 73
    * Starting at 0x4a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[14] == 0x526

    requires s0.stack[22] == 0x5c

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(15) == 0x526;
      assert s1.Peek(23) == 0x5c;
      assert s1.Peek(24) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 159
    * Segment Id for this node is: 74
    * Starting at 0x4a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[14] == 0x526

    requires s0.stack[22] == 0x5c

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x526;
      assert s1.Peek(22) == 0x5c;
      assert s1.Peek(23) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Dup6(s3);
      var s5 := Add(s4);
      var s6 := Dup11(s5);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push0(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(15) == 0x526;
      assert s11.Peek(23) == 0x5c;
      assert s11.Peek(24) == 0x61;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Dup10(s13);
      var s15 := Add(s14);
      var s16 := Swap3(s15);
      var s17 := Swap1(s16);
      var s18 := Swap3(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(13) == 0x526;
      assert s21.Peek(21) == 0x5c;
      assert s21.Peek(22) == 0x61;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Swap2(s23);
      var s25 := Dup5(s24);
      var s26 := Add(s25);
      var s27 := Swap2(s26);
      var s28 := Swap1(s27);
      var s29 := Dup5(s28);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(10) == 0x526;
      assert s31.Peek(18) == 0x5c;
      assert s31.Peek(19) == 0x61;
      var s32 := Push2(s31, 0x0445);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s33, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 75
    * Starting at 0x4c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -10
    * Net Capacity Effect: +10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x526

    requires s0.stack[18] == 0x5c

    requires s0.stack[19] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x526;
      assert s1.Peek(18) == 0x5c;
      assert s1.Peek(19) == 0x61;
      var s2 := Swap(s1, 10);
      var s3 := Swap(s2, 9);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x526;
      assert s11.Peek(10) == 0x5c;
      assert s11.Peek(11) == 0x61;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s13, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 82
    * Starting at 0x526
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x526 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x5c

    requires s0.stack[9] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x5c;
      assert s1.Peek(9) == 0x61;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap6(s5);
      var s7 := Swap2(s6);
      var s8 := Swap5(s7);
      var s9 := Pop(s8);
      var s10 := Swap3(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x5c;
      assert s11.Peek(5) == 0x61;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s12, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 9
    * Starting at 0x5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x61;
      var s2 := Push2(s1, 0x0103);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s3, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 19
    * Starting at 0x103
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x61;
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x61;
      var s12 := Push2(s11, 0x0153);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s166(s13, gas - 1)
      else
        ExecuteFromCFGNode_s164(s13, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 20
    * Starting at 0x116
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x61;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x61;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0e);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 14, 0x139bdd08185d5d1a1bdc9a5e9959);
      var s19 := Push1(s18, 0x92);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(7) == 0x61;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s165(s26, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 21
    * Starting at 0x14a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Revert(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 166
    * Segment Id for this node is: 22
    * Starting at 0x153
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x80);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup3(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(8) == 0x61;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := Dup7(s14);
      var s16 := Dup2(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup4(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(9) == 0x61;
      var s22 := Dup1(s21);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := Dup9(s24);
      var s26 := Dup2(s25);
      var s27 := MStore(s26);
      var s28 := Dup5(s27);
      var s29 := Dup7(s28);
      var s30 := Add(s29);
      var s31 := Dup9(s30);
      assert s31.Peek(12) == 0x61;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x60);
      var s35 := Dup7(s34);
      var s36 := Add(s35);
      var s37 := Dup9(s36);
      var s38 := Dup2(s37);
      var s39 := MStore(s38);
      var s40 := Push0(s39);
      var s41 := Swap5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s167(s41, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 23
    * Starting at 0x183
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x183 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(14) == 0x61;
      var s2 := MStore(s1);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := MStore(s4);
      var s6 := Swap7(s5);
      var s7 := Swap1(s6);
      var s8 := Swap4(s7);
      var s9 := Keccak256(s8);
      var s10 := Dup6(s9);
      var s11 := MLoad(s10);
      assert s11.Peek(12) == 0x61;
      var s12 := Dup2(s11);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := Not(s18);
      var s20 := And(s19);
      var s21 := Swap6(s20);
      assert s21.Peek(13) == 0x61;
      var s22 := And(s21);
      var s23 := Swap5(s22);
      var s24 := Swap1(s23);
      var s25 := Swap5(s24);
      var s26 := Or(s25);
      var s27 := Dup5(s26);
      var s28 := SStore(s27);
      var s29 := MLoad(s28);
      var s30 := Push1(s29, 0x01);
      var s31 := Dup5(s30);
      assert s31.Peek(12) == 0x61;
      var s32 := Add(s31);
      var s33 := SStore(s32);
      var s34 := Swap1(s33);
      var s35 := MLoad(s34);
      var s36 := Push1(s35, 0x02);
      var s37 := Dup4(s36);
      var s38 := Add(s37);
      var s39 := SStore(s38);
      var s40 := Swap3(s39);
      var s41 := MLoad(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s168(s41, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 24
    * Starting at 0x1b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(9) == 0x61;
      var s2 := MLoad(s1);
      var s3 := Swap3(s2);
      var s4 := Swap4(s3);
      var s5 := Swap2(s4);
      var s6 := Swap3(s5);
      var s7 := Push2(s6, 0x01c6);
      var s8 := Swap3(s7);
      var s9 := Push1(s8, 0x03);
      var s10 := Dup6(s9);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x1c6;
      assert s11.Peek(11) == 0x61;
      var s12 := Swap3(s11);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x02cb);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s16, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 31
    * Starting at 0x2cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1c6

    requires s0.stack[10] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1c6;
      assert s1.Peek(10) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := SStore(s6);
      var s8 := Swap1(s7);
      var s9 := Push0(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(5) == 0x1c6;
      assert s11.Peek(12) == 0x61;
      var s12 := Push0(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Swap3(s16);
      var s18 := Dup3(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x030f);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s21, gas - 1)
      else
        ExecuteFromCFGNode_s170(s21, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 32
    * Starting at 0x2e3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x1c6

    requires s0.stack[12] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0x1c6;
      assert s1.Peek(12) == 0x61;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s171(s5, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 33
    * Starting at 0x2e9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x1c6

    requires s0.stack[12] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1c6;
      assert s1.Peek(12) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x030f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s7, gas - 1)
      else
        ExecuteFromCFGNode_s172(s7, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 34
    * Starting at 0x2f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x1c6

    requires s0.stack[12] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(6) == 0x1c6;
      assert s1.Peek(13) == 0x61;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x02ff);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := Push2(s7, 0x0622);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s9, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 106
    * Starting at 0x622
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x622 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x2ff

    requires s0.stack[9] == 0x1c6

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2ff;
      assert s1.Peek(9) == 0x1c6;
      assert s1.Peek(16) == 0x61;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x063c);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s9, gas - 1)
      else
        ExecuteFromCFGNode_s174(s9, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 107
    * Starting at 0x635
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x635 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2ff

    requires s0.stack[10] == 0x1c6

    requires s0.stack[17] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x063c);
      assert s1.Peek(0) == 0x63c;
      assert s1.Peek(4) == 0x2ff;
      assert s1.Peek(11) == 0x1c6;
      assert s1.Peek(18) == 0x61;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s3, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x63c

    requires s0.stack[4] == 0x2ff

    requires s0.stack[11] == 0x1c6

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x63c;
      assert s1.Peek(4) == 0x2ff;
      assert s1.Peek(11) == 0x1c6;
      assert s1.Peek(18) == 0x61;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x63c;
      assert s11.Peek(6) == 0x2ff;
      assert s11.Peek(13) == 0x1c6;
      assert s11.Peek(20) == 0x61;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 176
    * Segment Id for this node is: 108
    * Starting at 0x63c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2ff

    requires s0.stack[10] == 0x1c6

    requires s0.stack[17] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ff;
      assert s1.Peek(10) == 0x1c6;
      assert s1.Peek(17) == 0x61;
      var s2 := Push2(s1, 0x0650);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x064a);
      var s5 := Dup5(s4);
      var s6 := SLoad(s5);
      var s7 := Push2(s6, 0x059e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s8, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 93
    * Starting at 0x59e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x64a

    requires s0.stack[3] == 0x650

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x1c6

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64a;
      assert s1.Peek(3) == 0x650;
      assert s1.Peek(7) == 0x2ff;
      assert s1.Peek(14) == 0x1c6;
      assert s1.Peek(21) == 0x61;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x05b2);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s179(s11, gas - 1)
      else
        ExecuteFromCFGNode_s178(s11, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 94
    * Starting at 0x5ac
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x64a

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x64a;
      assert s1.Peek(6) == 0x650;
      assert s1.Peek(10) == 0x2ff;
      assert s1.Peek(17) == 0x1c6;
      assert s1.Peek(24) == 0x61;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s179(s5, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 95
    * Starting at 0x5b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x64a

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x64a;
      assert s1.Peek(5) == 0x650;
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x1c6;
      assert s1.Peek(23) == 0x61;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x05d0);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s181(s8, gas - 1)
      else
        ExecuteFromCFGNode_s180(s8, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 96
    * Starting at 0x5bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x64a

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x64a;
      assert s1.Peek(6) == 0x650;
      assert s1.Peek(10) == 0x2ff;
      assert s1.Peek(17) == 0x1c6;
      assert s1.Peek(24) == 0x61;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 181
    * Segment Id for this node is: 97
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x64a

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x64a;
      assert s1.Peek(5) == 0x650;
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x1c6;
      assert s1.Peek(23) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s6, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 109
    * Starting at 0x64a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x650

    requires s0.stack[6] == 0x2ff

    requires s0.stack[13] == 0x1c6

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x650;
      assert s1.Peek(6) == 0x2ff;
      assert s1.Peek(13) == 0x1c6;
      assert s1.Peek(20) == 0x61;
      var s2 := Dup5(s1);
      var s3 := Push2(s2, 0x05d6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s4, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 98
    * Starting at 0x5d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x650

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x1c6

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x650;
      assert s1.Peek(7) == 0x2ff;
      assert s1.Peek(14) == 0x1c6;
      assert s1.Peek(21) == 0x61;
      var s2 := Push1(s1, 0x1f);
      var s3 := Dup3(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x061d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s190(s7, gas - 1)
      else
        ExecuteFromCFGNode_s184(s7, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 99
    * Starting at 0x5e0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x650

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x1c6

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x650;
      assert s1.Peek(8) == 0x2ff;
      assert s1.Peek(15) == 0x1c6;
      assert s1.Peek(22) == 0x61;
      var s2 := Push0(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push0(s4);
      var s6 := Keccak256(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x05);
      var s11 := Shr(s10);
      assert s11.Peek(5) == 0x650;
      assert s11.Peek(9) == 0x2ff;
      assert s11.Peek(16) == 0x1c6;
      assert s11.Peek(23) == 0x61;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup6(s14);
      var s16 := Lt(s15);
      var s17 := IsZero(s16);
      var s18 := Push2(s17, 0x05fb);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s19, gas - 1)
      else
        ExecuteFromCFGNode_s185(s19, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 100
    * Starting at 0x5f9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x650;
      assert s1.Peek(8) == 0x2ff;
      assert s1.Peek(15) == 0x1c6;
      assert s1.Peek(22) == 0x61;
      var s2 := Dup1(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s186(s2, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 101
    * Starting at 0x5fb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x650;
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x1c6;
      assert s1.Peek(23) == 0x61;
      var s2 := Push1(s1, 0x1f);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x05);
      var s6 := Shr(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Pop(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s187(s10, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 102
    * Starting at 0x607
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x607 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x650;
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x1c6;
      assert s1.Peek(23) == 0x61;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x061a);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s7, gas - 1)
      else
        ExecuteFromCFGNode_s188(s7, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 103
    * Starting at 0x610
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x610 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x650;
      assert s1.Peek(10) == 0x2ff;
      assert s1.Peek(17) == 0x1c6;
      assert s1.Peek(24) == 0x61;
      var s2 := Dup2(s1);
      var s3 := SStore(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Add(s4);
      var s6 := Push2(s5, 0x0607);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s7, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 104
    * Starting at 0x61a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0x650

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x650;
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x1c6;
      assert s1.Peek(23) == 0x61;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s190(s3, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 105
    * Starting at 0x61d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x650

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x1c6

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x650;
      assert s1.Peek(7) == 0x2ff;
      assert s1.Peek(14) == 0x1c6;
      assert s1.Peek(21) == 0x61;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s5, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 110
    * Starting at 0x650
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x650 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2ff

    requires s0.stack[10] == 0x1c6

    requires s0.stack[17] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ff;
      assert s1.Peek(10) == 0x1c6;
      assert s1.Peek(17) == 0x61;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Gt(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Dup2(s7);
      var s9 := Eq(s8);
      var s10 := Push2(s9, 0x0683);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s11, gas - 1)
      else
        ExecuteFromCFGNode_s192(s11, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 111
    * Starting at 0x660
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x660 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x2ff

    requires s0.stack[13] == 0x1c6

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x2ff;
      assert s1.Peek(14) == 0x1c6;
      assert s1.Peek(21) == 0x61;
      var s2 := Dup5(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x066c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s5, gas - 1)
      else
        ExecuteFromCFGNode_s193(s5, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 112
    * Starting at 0x667
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x667 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x1c6

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(6) == 0x2ff;
      assert s1.Peek(13) == 0x1c6;
      assert s1.Peek(20) == 0x61;
      var s2 := Dup6(s1);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s194(s5, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 113
    * Starting at 0x66c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[7] == 0x2ff

    requires s0.stack[14] == 0x1c6

    requires s0.stack[21] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x2ff;
      assert s1.Peek(14) == 0x1c6;
      assert s1.Peek(21) == 0x61;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Push1(s3, 0x03);
      var s5 := Dup7(s4);
      var s6 := Swap1(s5);
      var s7 := Shl(s6);
      var s8 := Shr(s7);
      var s9 := Not(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(8) == 0x2ff;
      assert s11.Peek(15) == 0x1c6;
      assert s11.Peek(22) == 0x61;
      var s12 := Dup6(s11);
      var s13 := Swap1(s12);
      var s14 := Shl(s13);
      var s15 := Or(s14);
      var s16 := Dup6(s15);
      var s17 := SStore(s16);
      var s18 := Push2(s17, 0x06da);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s19, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 120
    * Starting at 0x6da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x2ff

    requires s0.stack[13] == 0x1c6

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2ff;
      assert s1.Peek(13) == 0x1c6;
      assert s1.Peek(20) == 0x61;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s8, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 35
    * Starting at 0x2ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[6] == 0x1c6

    requires s0.stack[13] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1c6;
      assert s1.Peek(13) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x02e9);
      assert s11.Peek(0) == 0x2e9;
      assert s11.Peek(6) == 0x1c6;
      assert s11.Peek(13) == 0x61;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s12, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 114
    * Starting at 0x683
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x683 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x2ff

    requires s0.stack[13] == 0x1c6

    requires s0.stack[20] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2ff;
      assert s1.Peek(13) == 0x1c6;
      assert s1.Peek(20) == 0x61;
      var s2 := Push0(s1);
      var s3 := Dup6(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Keccak256(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Not(s9);
      var s11 := Dup7(s10);
      assert s11.Peek(10) == 0x2ff;
      assert s11.Peek(17) == 0x1c6;
      assert s11.Peek(24) == 0x61;
      var s12 := And(s11);
      var s13 := Swap2(s12);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s198(s13, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 115
    * Starting at 0x692
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x692 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x1c6;
      assert s1.Peek(23) == 0x61;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x06b1);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s200(s7, gas - 1)
      else
        ExecuteFromCFGNode_s199(s7, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 116
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup9(s0);
      assert s1.Peek(10) == 0x2ff;
      assert s1.Peek(17) == 0x1c6;
      assert s1.Peek(24) == 0x61;
      var s2 := Dup7(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup3(s4);
      var s6 := SStore(s5);
      var s7 := Swap5(s6);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := Swap5(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(10) == 0x2ff;
      assert s11.Peek(17) == 0x1c6;
      assert s11.Peek(24) == 0x61;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := Add(s13);
      var s15 := Swap1(s14);
      var s16 := Dup5(s15);
      var s17 := Add(s16);
      var s18 := Push2(s17, 0x0692);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s19, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 117
    * Starting at 0x6b1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[9] == 0x2ff

    requires s0.stack[16] == 0x1c6

    requires s0.stack[23] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x1c6;
      assert s1.Peek(23) == 0x61;
      var s2 := Pop(s1);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x06ce);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s8, gas - 1)
      else
        ExecuteFromCFGNode_s201(s8, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 118
    * Starting at 0x6bb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[8] == 0x2ff

    requires s0.stack[15] == 0x1c6

    requires s0.stack[22] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup8(s0);
      assert s1.Peek(9) == 0x2ff;
      assert s1.Peek(16) == 0x1c6;
      assert s1.Peek(23) == 0x61;
      var s2 := Dup6(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Push0(s4);
      var s6 := Not(s5);
      var s7 := Push1(s6, 0x03);
      var s8 := Dup9(s7);
      var s9 := Swap1(s8);
      var s10 := Shl(s9);
      var s11 := Push1(s10, 0xf8);
      assert s11.Peek(12) == 0x2ff;
      assert s11.Peek(19) == 0x1c6;
      assert s11.Peek(26) == 0x61;
      var s12 := And(s11);
      var s13 := Shr(s12);
      var s14 := Not(s13);
      var s15 := And(s14);
      var s16 := Dup2(s15);
      var s17 := SStore(s16);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s202(s17, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 119
    * Starting at 0x6ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[8] == 0x2ff

    requires s0.stack[15] == 0x1c6

    requires s0.stack[22] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x2ff;
      assert s1.Peek(15) == 0x1c6;
      assert s1.Peek(22) == 0x61;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Shl(s6);
      var s8 := Add(s7);
      var s9 := Dup6(s8);
      var s10 := SStore(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s195(s10, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 36
    * Starting at 0x30f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x1c6

    requires s0.stack[12] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1c6;
      assert s1.Peek(12) == 0x61;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x031b);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x031f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s8, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 38
    * Starting at 0x31f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x31b

    requires s0.stack[4] == 0x1c6

    requires s0.stack[11] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31b;
      assert s1.Peek(4) == 0x1c6;
      assert s1.Peek(11) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x031b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s221(s7, gas - 1)
      else
        ExecuteFromCFGNode_s205(s7, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 39
    * Starting at 0x328
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x328 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x31b

    requires s0.stack[4] == 0x1c6

    requires s0.stack[11] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x31b;
      assert s1.Peek(5) == 0x1c6;
      assert s1.Peek(12) == 0x61;
      var s2 := Push2(s1, 0x0332);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x033b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s6, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 41
    * Starting at 0x33b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x332

    requires s0.stack[6] == 0x31b

    requires s0.stack[8] == 0x1c6

    requires s0.stack[15] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x332;
      assert s1.Peek(6) == 0x31b;
      assert s1.Peek(8) == 0x1c6;
      assert s1.Peek(15) == 0x61;
      var s2 := Pop(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x0347);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x059e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s8, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 93
    * Starting at 0x59e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x347

    requires s0.stack[3] == 0x332

    requires s0.stack[7] == 0x31b

    requires s0.stack[9] == 0x1c6

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x347;
      assert s1.Peek(3) == 0x332;
      assert s1.Peek(7) == 0x31b;
      assert s1.Peek(9) == 0x1c6;
      assert s1.Peek(16) == 0x61;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x05b2);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s209(s11, gas - 1)
      else
        ExecuteFromCFGNode_s208(s11, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 94
    * Starting at 0x5ac
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x347

    requires s0.stack[5] == 0x332

    requires s0.stack[9] == 0x31b

    requires s0.stack[11] == 0x1c6

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x347;
      assert s1.Peek(6) == 0x332;
      assert s1.Peek(10) == 0x31b;
      assert s1.Peek(12) == 0x1c6;
      assert s1.Peek(19) == 0x61;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s209(s5, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 95
    * Starting at 0x5b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x347

    requires s0.stack[5] == 0x332

    requires s0.stack[9] == 0x31b

    requires s0.stack[11] == 0x1c6

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x347;
      assert s1.Peek(5) == 0x332;
      assert s1.Peek(9) == 0x31b;
      assert s1.Peek(11) == 0x1c6;
      assert s1.Peek(18) == 0x61;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x05d0);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s211(s8, gas - 1)
      else
        ExecuteFromCFGNode_s210(s8, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 96
    * Starting at 0x5bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x347

    requires s0.stack[5] == 0x332

    requires s0.stack[9] == 0x31b

    requires s0.stack[11] == 0x1c6

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x347;
      assert s1.Peek(6) == 0x332;
      assert s1.Peek(10) == 0x31b;
      assert s1.Peek(12) == 0x1c6;
      assert s1.Peek(19) == 0x61;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 211
    * Segment Id for this node is: 97
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x347

    requires s0.stack[5] == 0x332

    requires s0.stack[9] == 0x31b

    requires s0.stack[11] == 0x1c6

    requires s0.stack[18] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x347;
      assert s1.Peek(5) == 0x332;
      assert s1.Peek(9) == 0x31b;
      assert s1.Peek(11) == 0x1c6;
      assert s1.Peek(18) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s6, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 42
    * Starting at 0x347
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x347 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x332

    requires s0.stack[6] == 0x31b

    requires s0.stack[8] == 0x1c6

    requires s0.stack[15] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x332;
      assert s1.Peek(6) == 0x31b;
      assert s1.Peek(8) == 0x1c6;
      assert s1.Peek(15) == 0x61;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := SStore(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Lt(s6);
      var s8 := Push2(s7, 0x0356);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s215(s9, gas - 1)
      else
        ExecuteFromCFGNode_s213(s9, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 43
    * Starting at 0x353
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x353 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x332

    requires s0.stack[6] == 0x31b

    requires s0.stack[8] == 0x1c6

    requires s0.stack[15] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0x332;
      assert s1.Peek(5) == 0x31b;
      assert s1.Peek(7) == 0x1c6;
      assert s1.Peek(14) == 0x61;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s3, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 40
    * Starting at 0x332
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x332 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x31b

    requires s0.stack[5] == 0x1c6

    requires s0.stack[12] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x31b;
      assert s1.Peek(5) == 0x1c6;
      assert s1.Peek(12) == 0x61;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Add(s3);
      var s5 := Push2(s4, 0x031f);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s6, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 44
    * Starting at 0x356
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x356 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x332

    requires s0.stack[6] == 0x31b

    requires s0.stack[8] == 0x1c6

    requires s0.stack[15] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x332;
      assert s1.Peek(6) == 0x31b;
      assert s1.Peek(8) == 0x1c6;
      assert s1.Peek(15) == 0x61;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Swap1(s4);
      var s6 := Div(s5);
      var s7 := Swap1(s6);
      var s8 := Push0(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push0(s10);
      assert s11.Peek(3) == 0x332;
      assert s11.Peek(7) == 0x31b;
      assert s11.Peek(9) == 0x1c6;
      assert s11.Peek(16) == 0x61;
      var s12 := Keccak256(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Push2(s16, 0x0372);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Push2(s19, 0x0375);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s21, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 46
    * Starting at 0x375
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x375 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x372

    requires s0.stack[3] == 0x332

    requires s0.stack[7] == 0x31b

    requires s0.stack[9] == 0x1c6

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s217(s1, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 47
    * Starting at 0x376
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x376 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x372

    requires s0.stack[3] == 0x332

    requires s0.stack[7] == 0x31b

    requires s0.stack[9] == 0x1c6

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x372;
      assert s1.Peek(3) == 0x332;
      assert s1.Peek(7) == 0x31b;
      assert s1.Peek(9) == 0x1c6;
      assert s1.Peek(16) == 0x61;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x031b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s219(s7, gas - 1)
      else
        ExecuteFromCFGNode_s218(s7, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 48
    * Starting at 0x37f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x372

    requires s0.stack[3] == 0x332

    requires s0.stack[7] == 0x31b

    requires s0.stack[9] == 0x1c6

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(4) == 0x332;
      assert s1.Peek(8) == 0x31b;
      assert s1.Peek(10) == 0x1c6;
      assert s1.Peek(17) == 0x61;
      var s2 := Dup2(s1);
      var s3 := SStore(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Add(s4);
      var s6 := Push2(s5, 0x0376);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s7, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 37
    * Starting at 0x31b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x372

    requires s0.stack[3] == 0x332

    requires s0.stack[7] == 0x31b

    requires s0.stack[9] == 0x1c6

    requires s0.stack[16] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x372;
      assert s1.Peek(3) == 0x332;
      assert s1.Peek(7) == 0x31b;
      assert s1.Peek(9) == 0x1c6;
      assert s1.Peek(16) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s4, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 45
    * Starting at 0x372
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x372 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x332

    requires s0.stack[5] == 0x31b

    requires s0.stack[7] == 0x1c6

    requires s0.stack[14] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x332;
      assert s1.Peek(5) == 0x31b;
      assert s1.Peek(7) == 0x1c6;
      assert s1.Peek(14) == 0x61;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s3, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 37
    * Starting at 0x31b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x31b

    requires s0.stack[4] == 0x1c6

    requires s0.stack[11] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31b;
      assert s1.Peek(4) == 0x1c6;
      assert s1.Peek(11) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s4, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 37
    * Starting at 0x31b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1c6

    requires s0.stack[9] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c6;
      assert s1.Peek(9) == 0x61;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s4, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 25
    * Starting at 0x1c6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x61;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Dup7(s10);
      assert s11.Peek(8) == 0x61;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push32(s14, 0xa7dff163671e610b2bf8ca2e049a3f29bd4e483b11bed1545b16d733ff17780b);
      var s16 := Swap2(s15);
      var s17 := Pop(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Add(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s108(s19, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 7
    * Starting at 0x4a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }
}
