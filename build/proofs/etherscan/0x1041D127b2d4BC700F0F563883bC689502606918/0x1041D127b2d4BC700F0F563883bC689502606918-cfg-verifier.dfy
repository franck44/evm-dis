include "../../../../src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module  {:disableNonlinearArithmetic} EVMProofObject {

  import opened AbstractSemantics
  import opened AbstractState

  /** Node 0
    * Segment Id for this node is: 0
    * Starting at 0x0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
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
      var s4 := Push1(s3, 0x04);
      var s5 := CallDataSize(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x00d6);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s358(s8, gas - 1)
      else
        ExecuteFromCFGNode_s1(s8, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0xd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shr(s3);
      var s5 := Dup1(s4);
      var s6 := Push4(s5, 0x8c70830b);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x007f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s167(s9, gas - 1)
      else
        ExecuteFromCFGNode_s2(s9, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x1e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xbeabacc8);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0059);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s5, gas - 1)
      else
        ExecuteFromCFGNode_s3(s5, gas - 1)
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
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xbeabacc8);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x022e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s5, gas - 1)
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
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xc859c483);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x024e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s5, gas - 1)
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
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x026e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s13(s5, gas - 1)
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
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf851a440);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x028e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x55
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 8
    * Segment Id for this node is: 73
    * Starting at 0x28e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x029a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s6, gas - 1)
      else
        ExecuteFromCFGNode_s9(s6, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 74
    * Starting at 0x296
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
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

  /** Node 10
    * Segment Id for this node is: 75
    * Starting at 0x29a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x01f6);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0x1f6;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s14, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 56
    * Starting at 0x1f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1f6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1f6;
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
      assert s11.Peek(2) == 0x1f6;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0140);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s17, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 34
    * Starting at 0x140
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1f6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1f6;
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

  /** Node 13
    * Segment Id for this node is: 69
    * Starting at 0x26e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x027a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s6, gas - 1)
      else
        ExecuteFromCFGNode_s14(s6, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 70
    * Starting at 0x276
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x276 as nat
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

  /** Node 15
    * Segment Id for this node is: 71
    * Starting at 0x27a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0102);
      var s4 := Push2(s3, 0x0289);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0b72);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s8, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 174
    * Starting at 0xb72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x289

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x289;
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0b84);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s18(s10, gas - 1)
      else
        ExecuteFromCFGNode_s17(s10, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 175
    * Starting at 0xb80
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x289

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x289;
      assert s1.Peek(5) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 18
    * Segment Id for this node is: 176
    * Starting at 0xb84
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x289

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x289;
      assert s1.Peek(4) == 0x102;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0b8f);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b16);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s7, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x289

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0x289;
      assert s1.Peek(7) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xb8f;
      assert s11.Peek(8) == 0x289;
      assert s11.Peek(9) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s12, gas - 1)
      else
        ExecuteFromCFGNode_s20(s12, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x289

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb8f;
      assert s1.Peek(7) == 0x289;
      assert s1.Peek(8) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 21
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x289

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0x289;
      assert s1.Peek(7) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s3, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 177
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x289

    requires s0.stack[5] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x289;
      assert s1.Peek(5) == 0x102;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s7, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 72
    * Starting at 0x289
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x289 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push2(s1, 0x06d4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s3, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 124
    * Starting at 0x6d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push2(s1, 0x06dc);
      var s3 := Push2(s2, 0x0783);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s4, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 130
    * Starting at 0x783
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x783 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x6dc

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6dc;
      assert s1.Peek(2) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x6dc;
      assert s11.Peek(3) == 0x102;
      var s12 := Push2(s11, 0x04c3);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s13, gas - 1)
      else
        ExecuteFromCFGNode_s26(s13, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 131
    * Starting at 0x796
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x796 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x6dc

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x6dc;
      assert s1.Peek(3) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x6dc;
      assert s11.Peek(6) == 0x102;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(1) == 0x6dc;
      assert s21.Peek(3) == 0x102;
      var s22 := Push1(s21, 0x64);
      var s23 := Add(s22);
      var s24 := Push2(s23, 0x076e);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s25, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 127
    * Starting at 0x76e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x6dc

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6dc;
      assert s1.Peek(3) == 0x102;
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

  /** Node 28
    * Segment Id for this node is: 99
    * Starting at 0x4c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x6dc

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6dc;
      assert s1.Peek(2) == 0x102;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s2, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 125
    * Starting at 0x6dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0777);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s32(s10, gas - 1)
      else
        ExecuteFromCFGNode_s30(s10, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 126
    * Starting at 0x6eb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x26);
      assert s11.Peek(3) == 0x102;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x4f776e61626c653a206e6577206f776e657220697320746865207a65726f2061);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x6464726573730000000000000000000000000000000000000000000000000000);
      assert s21.Peek(3) == 0x102;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s31(s27, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 127
    * Starting at 0x76e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
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

  /** Node 32
    * Segment Id for this node is: 128
    * Starting at 0x777
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x777 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push2(s1, 0x0780);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x081d);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s5, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 136
    * Starting at 0x81d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x780

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x780;
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup4(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x780;
      assert s11.Peek(8) == 0x102;
      var s12 := And(s11);
      var s13 := Push32(s12, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000);
      var s14 := Dup4(s13);
      var s15 := And(s14);
      var s16 := Dup2(s15);
      var s17 := Or(s16);
      var s18 := Dup5(s17);
      var s19 := SStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := MLoad(s20);
      assert s21.Peek(6) == 0x780;
      assert s21.Peek(8) == 0x102;
      var s22 := Swap2(s21);
      var s23 := Swap1(s22);
      var s24 := Swap3(s23);
      var s25 := And(s24);
      var s26 := Swap3(s25);
      var s27 := Dup4(s26);
      var s28 := Swap2(s27);
      var s29 := Push32(s28, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s30 := Swap2(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x780;
      assert s31.Peek(9) == 0x102;
      var s32 := Log3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s35, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s3, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 28
    * Starting at 0x102
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102 as nat
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

  /** Node 36
    * Segment Id for this node is: 65
    * Starting at 0x24e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x025a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s6, gas - 1)
      else
        ExecuteFromCFGNode_s37(s6, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 66
    * Starting at 0x256
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x256 as nat
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

  /** Node 38
    * Segment Id for this node is: 67
    * Starting at 0x25a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0102);
      var s4 := Push2(s3, 0x0269);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0c1c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s8, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 190
    * Starting at 0xc1c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x269

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x269;
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0c2f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s11, gas - 1)
      else
        ExecuteFromCFGNode_s40(s11, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 191
    * Starting at 0xc2b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x269

    requires s0.stack[5] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x269;
      assert s1.Peek(6) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 41
    * Segment Id for this node is: 192
    * Starting at 0xc2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x269

    requires s0.stack[5] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x269;
      assert s1.Peek(5) == 0x102;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0c3a);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b16);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s7, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xc3a

    requires s0.stack[7] == 0x269

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc3a;
      assert s1.Peek(7) == 0x269;
      assert s1.Peek(8) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xc3a;
      assert s11.Peek(9) == 0x269;
      assert s11.Peek(10) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s44(s12, gas - 1)
      else
        ExecuteFromCFGNode_s43(s12, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xc3a

    requires s0.stack[7] == 0x269

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xc3a;
      assert s1.Peek(8) == 0x269;
      assert s1.Peek(9) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 44
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xc3a

    requires s0.stack[7] == 0x269

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc3a;
      assert s1.Peek(7) == 0x269;
      assert s1.Peek(8) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s3, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 193
    * Starting at 0xc3a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x269

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x269;
      assert s1.Peek(6) == 0x102;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push8(s7, 0xffffffffffffffff);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x269;
      assert s11.Peek(8) == 0x102;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b67);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s14, gas - 1)
      else
        ExecuteFromCFGNode_s46(s14, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 194
    * Starting at 0xc53
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc53 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x269

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x269;
      assert s1.Peek(7) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 47
    * Segment Id for this node is: 173
    * Starting at 0xb67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x269

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x269;
      assert s1.Peek(6) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Swap3(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s11, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 68
    * Starting at 0x269
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x269 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
      var s2 := Push2(s1, 0x05e9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s3, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 114
    * Starting at 0x5e9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
      var s2 := Push1(s1, 0x02);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(3) == 0x102;
      var s12 := Push2(s11, 0x0613);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s13, gas - 1)
      else
        ExecuteFromCFGNode_s50(s13, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 115
    * Starting at 0x5fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x82b429);
      var s4 := Push1(s3, 0xe8);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(4) == 0x102;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 51
    * Segment Id for this node is: 116
    * Starting at 0x613
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x613 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x102;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(4) == 0x102;
      var s22 := Push1(s21, 0xff);
      var s23 := And(s22);
      var s24 := Push2(s23, 0x064d);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s25, gas - 1)
      else
        ExecuteFromCFGNode_s52(s25, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 117
    * Starting at 0x636
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x636 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x82b429);
      var s4 := Push1(s3, 0xe8);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(5) == 0x102;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 53
    * Segment Id for this node is: 118
    * Starting at 0x64d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xc859c48300000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Address(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x102;
      var s12 := Push8(s11, 0xffffffffffffffff);
      var s13 := Dup4(s12);
      var s14 := And(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0xa0);
      assert s21.Peek(7) == 0x102;
      var s22 := Shl(s21);
      var s23 := Sub(s22);
      var s24 := Dup5(s23);
      var s25 := And(s24);
      var s26 := Swap1(s25);
      var s27 := Push4(s26, 0xc859c483);
      var s28 := Swap1(s27);
      var s29 := Push1(s28, 0x44);
      var s30 := Add(s29);
      var s31 := Push1(s30, 0x00);
      assert s31.Peek(7) == 0x102;
      var s32 := Push1(s31, 0x40);
      var s33 := MLoad(s32);
      var s34 := Dup1(s33);
      var s35 := Dup4(s34);
      var s36 := Sub(s35);
      var s37 := Dup2(s36);
      var s38 := Push1(s37, 0x00);
      var s39 := Dup8(s38);
      var s40 := Dup1(s39);
      var s41 := ExtCodeSize(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s54(s41, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 119
    * Starting at 0x6ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := IsZero(s0);
      assert s1.Peek(13) == 0x102;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x06b7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s5, gas - 1)
      else
        ExecuteFromCFGNode_s55(s5, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 120
    * Starting at 0x6b3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(14) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 56
    * Segment Id for this node is: 121
    * Starting at 0x6b7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x102;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x06cb);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s9, gas - 1)
      else
        ExecuteFromCFGNode_s57(s9, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 122
    * Starting at 0x6c2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(8) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 58
    * Segment Id for this node is: 123
    * Starting at 0x6cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s9, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 61
    * Starting at 0x22e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x023a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s6, gas - 1)
      else
        ExecuteFromCFGNode_s60(s6, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 62
    * Starting at 0x236
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x236 as nat
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

  /** Node 61
    * Segment Id for this node is: 63
    * Starting at 0x23a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0102);
      var s4 := Push2(s3, 0x0249);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0bdb);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s8, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 185
    * Starting at 0xbdb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x249

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x249;
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0bf0);
      assert s11.Peek(0) == 0xbf0;
      assert s11.Peek(7) == 0x249;
      assert s11.Peek(8) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s12, gas - 1)
      else
        ExecuteFromCFGNode_s63(s12, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 186
    * Starting at 0xbec
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x249

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x249;
      assert s1.Peek(7) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 64
    * Segment Id for this node is: 187
    * Starting at 0xbf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x249

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x249;
      assert s1.Peek(6) == 0x102;
      var s2 := Dup4(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0bfb);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b16);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s7, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xbfb

    requires s0.stack[8] == 0x249

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbfb;
      assert s1.Peek(8) == 0x249;
      assert s1.Peek(9) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xbfb;
      assert s11.Peek(10) == 0x249;
      assert s11.Peek(11) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s12, gas - 1)
      else
        ExecuteFromCFGNode_s66(s12, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xbfb

    requires s0.stack[8] == 0x249

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xbfb;
      assert s1.Peek(9) == 0x249;
      assert s1.Peek(10) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 67
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xbfb

    requires s0.stack[8] == 0x249

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbfb;
      assert s1.Peek(8) == 0x249;
      assert s1.Peek(9) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s3, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 188
    * Starting at 0xbfb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x249

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x249;
      assert s1.Peek(7) == 0x102;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x0c0b);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x0b16);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s11, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xc0b

    requires s0.stack[8] == 0x249

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc0b;
      assert s1.Peek(8) == 0x249;
      assert s1.Peek(9) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xc0b;
      assert s11.Peek(10) == 0x249;
      assert s11.Peek(11) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s12, gas - 1)
      else
        ExecuteFromCFGNode_s70(s12, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xc0b

    requires s0.stack[8] == 0x249

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xc0b;
      assert s1.Peek(9) == 0x249;
      assert s1.Peek(10) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 71
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xc0b

    requires s0.stack[8] == 0x249

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc0b;
      assert s1.Peek(8) == 0x249;
      assert s1.Peek(9) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s3, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 189
    * Starting at 0xc0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x249

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x249;
      assert s1.Peek(7) == 0x102;
      var s2 := Swap3(s1);
      var s3 := Swap6(s2);
      var s4 := Swap3(s3);
      var s5 := Swap5(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(0) == 0x249;
      assert s11.Peek(5) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s16, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 64
    * Starting at 0x249
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x249 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      var s2 := Push2(s1, 0x05cf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s3, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 111
    * Starting at 0x5cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      var s2 := Push2(s1, 0x05d7);
      var s3 := Push2(s2, 0x0783);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s4, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 130
    * Starting at 0x783
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x783 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x5d7

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5d7;
      assert s1.Peek(4) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x5d7;
      assert s11.Peek(5) == 0x102;
      var s12 := Push2(s11, 0x04c3);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s13, gas - 1)
      else
        ExecuteFromCFGNode_s76(s13, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 131
    * Starting at 0x796
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x796 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x5d7

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x5d7;
      assert s1.Peek(5) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x5d7;
      assert s11.Peek(8) == 0x102;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(1) == 0x5d7;
      assert s21.Peek(5) == 0x102;
      var s22 := Push1(s21, 0x64);
      var s23 := Add(s22);
      var s24 := Push2(s23, 0x076e);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s25, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 127
    * Starting at 0x76e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x5d7

    requires s0.stack[5] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5d7;
      assert s1.Peek(5) == 0x102;
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

  /** Node 78
    * Segment Id for this node is: 99
    * Starting at 0x4c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x5d7

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5d7;
      assert s1.Peek(4) == 0x102;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s2, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 112
    * Starting at 0x5d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      var s2 := Push2(s1, 0x05e4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Push2(s6, 0x0885);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s8, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 137
    * Starting at 0x885
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x885 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x5e4

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5e4;
      assert s1.Peek(8) == 0x102;
      var s2 := Push2(s1, 0x0891);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x09e0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s8, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 147
    * Starting at 0x9e0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x891

    requires s0.stack[9] == 0x5e4

    requires s0.stack[13] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x891;
      assert s1.Peek(9) == 0x5e4;
      assert s1.Peek(13) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup6(s7);
      var s9 := And(s8);
      var s10 := Push2(s9, 0x0a02);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s11, gas - 1)
      else
        ExecuteFromCFGNode_s82(s11, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 148
    * Starting at 0x9f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x891

    requires s0.stack[10] == 0x5e4

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09fb);
      assert s1.Peek(0) == 0x9fb;
      assert s1.Peek(6) == 0x891;
      assert s1.Peek(11) == 0x5e4;
      assert s1.Peek(15) == 0x102;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Push2(s4, 0x0aa3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s6, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 160
    * Starting at 0xaa3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x9fb

    requires s0.stack[9] == 0x891

    requires s0.stack[14] == 0x5e4

    requires s0.stack[18] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9fb;
      assert s1.Peek(9) == 0x891;
      assert s1.Peek(14) == 0x5e4;
      assert s1.Peek(18) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0ab1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s6, gas - 1)
      else
        ExecuteFromCFGNode_s84(s6, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 161
    * Starting at 0xaac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0x9fb

    requires s0.stack[11] == 0x891

    requires s0.stack[16] == 0x5e4

    requires s0.stack[20] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Gas(s0);
      assert s1.Peek(6) == 0x9fb;
      assert s1.Peek(12) == 0x891;
      assert s1.Peek(17) == 0x5e4;
      assert s1.Peek(21) == 0x102;
      var s2 := Push2(s1, 0x0ab5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s3, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 163
    * Starting at 0xab5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[6] == 0x9fb

    requires s0.stack[12] == 0x891

    requires s0.stack[17] == 0x5e4

    requires s0.stack[21] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x9fb;
      assert s1.Peek(12) == 0x891;
      assert s1.Peek(17) == 0x5e4;
      assert s1.Peek(21) == 0x102;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Dup1(s6);
      var s8 := Dup8(s7);
      var s9 := Dup10(s8);
      var s10 := Dup7(s9);
      var s11 := Call(s10);
      assert s11.Peek(6) == 0x9fb;
      assert s11.Peek(12) == 0x891;
      assert s11.Peek(17) == 0x5e4;
      assert s11.Peek(21) == 0x102;
      var s12 := Swap6(s11);
      var s13 := Swap5(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s19, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 149
    * Starting at 0x9fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[6] == 0x891

    requires s0.stack[11] == 0x5e4

    requires s0.stack[15] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x891;
      assert s1.Peek(11) == 0x5e4;
      assert s1.Peek(15) == 0x102;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0997);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s5, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 143
    * Starting at 0x997
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x997 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x891

    requires s0.stack[10] == 0x5e4

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x891;
      assert s1.Peek(10) == 0x5e4;
      assert s1.Peek(14) == 0x102;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s8, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 138
    * Starting at 0x891
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x5e4

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x5e4;
      assert s1.Peek(9) == 0x102;
      var s2 := Push2(s1, 0x08c7);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s3, gas - 1)
      else
        ExecuteFromCFGNode_s89(s3, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 139
    * Starting at 0x896
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x896 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x5e4

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x5e4;
      assert s1.Peek(9) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x7c75c3d200000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MLoad(s8);
      var s10 := Dup1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(7) == 0x5e4;
      assert s11.Peek(11) == 0x102;
      var s12 := Sub(s11);
      var s13 := Swap1(s12);
      var s14 := Revert(s13);
      // Segment is terminal (Revert, Stop or Return)
      s14
  }

  /** Node 90
    * Segment Id for this node is: 140
    * Starting at 0x8c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x5e4

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5e4;
      assert s1.Peek(8) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s6, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 113
    * Starting at 0x5e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s5, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 162
    * Starting at 0xab1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0x9fb

    requires s0.stack[11] == 0x891

    requires s0.stack[16] == 0x5e4

    requires s0.stack[20] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x9fb;
      assert s1.Peek(11) == 0x891;
      assert s1.Peek(16) == 0x5e4;
      assert s1.Peek(20) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s85(s3, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 150
    * Starting at 0xa02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x891

    requires s0.stack[10] == 0x5e4

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x891;
      assert s1.Peek(10) == 0x5e4;
      assert s1.Peek(14) == 0x102;
      var s2 := Push2(s1, 0x0a0d);
      var s3 := Dup6(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Push2(s5, 0x0aca);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s7, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 164
    * Starting at 0xaca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xa0d

    requires s0.stack[9] == 0x891

    requires s0.stack[14] == 0x5e4

    requires s0.stack[18] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa0d;
      assert s1.Peek(9) == 0x891;
      assert s1.Peek(14) == 0x5e4;
      assert s1.Peek(18) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x24);
      assert s11.Peek(6) == 0xa0d;
      assert s11.Peek(12) == 0x891;
      assert s11.Peek(17) == 0x5e4;
      assert s11.Peek(21) == 0x102;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x44);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup3(s17);
      var s19 := Swap1(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0xa0d;
      assert s21.Peek(11) == 0x891;
      assert s21.Peek(16) == 0x5e4;
      assert s21.Peek(20) == 0x102;
      var s22 := Swap1(s21);
      var s23 := Push2(s22, 0x0997);
      var s24 := Swap1(s23);
      var s25 := Dup6(s24);
      var s26 := Swap1(s25);
      var s27 := Push32(s26, 0xa9059cbb00000000000000000000000000000000000000000000000000000000);
      var s28 := Swap1(s27);
      var s29 := Push1(s28, 0x64);
      var s30 := Add(s29);
      var s31 := Push2(s30, 0x0915);
      assert s31.Peek(0) == 0x915;
      assert s31.Peek(4) == 0x997;
      assert s31.Peek(9) == 0xa0d;
      assert s31.Peek(15) == 0x891;
      assert s31.Peek(20) == 0x5e4;
      assert s31.Peek(24) == 0x102;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s32, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 142
    * Starting at 0x915
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x915 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x997

    requires s0.stack[8] == 0xa0d

    requires s0.stack[14] == 0x891

    requires s0.stack[19] == 0x5e4

    requires s0.stack[23] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x997;
      assert s1.Peek(8) == 0xa0d;
      assert s1.Peek(14) == 0x891;
      assert s1.Peek(19) == 0x5e4;
      assert s1.Peek(23) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x997;
      assert s11.Peek(10) == 0xa0d;
      assert s11.Peek(16) == 0x891;
      assert s11.Peek(21) == 0x5e4;
      assert s11.Peek(25) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := PushN(s19, 28, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(5) == 0x997;
      assert s21.Peek(10) == 0xa0d;
      assert s21.Peek(16) == 0x891;
      assert s21.Peek(21) == 0x5e4;
      assert s21.Peek(25) == 0x102;
      var s22 := Push32(s21, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := And(s24);
      var s26 := Swap3(s25);
      var s27 := Swap1(s26);
      var s28 := Swap3(s27);
      var s29 := Or(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(4) == 0x997;
      assert s31.Peek(9) == 0xa0d;
      assert s31.Peek(15) == 0x891;
      assert s31.Peek(20) == 0x5e4;
      assert s31.Peek(24) == 0x102;
      var s32 := MStore(s31);
      var s33 := Push2(s32, 0x0a16);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s34, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 152
    * Starting at 0xa16
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x997

    requires s0.stack[7] == 0xa0d

    requires s0.stack[13] == 0x891

    requires s0.stack[18] == 0x5e4

    requires s0.stack[22] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x997;
      assert s1.Peek(7) == 0xa0d;
      assert s1.Peek(13) == 0x891;
      assert s1.Peek(18) == 0x5e4;
      assert s1.Peek(22) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x997;
      assert s11.Peek(11) == 0xa0d;
      assert s11.Peek(17) == 0x891;
      assert s11.Peek(22) == 0x5e4;
      assert s11.Peek(26) == 0x102;
      var s12 := Dup5(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0a33);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x0c8d);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s19, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 201
    * Starting at 0xc8d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[2] == 0xa33

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0xa0d

    requires s0.stack[20] == 0x891

    requires s0.stack[25] == 0x5e4

    requires s0.stack[29] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa33;
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0xa0d;
      assert s1.Peek(20) == 0x891;
      assert s1.Peek(25) == 0x5e4;
      assert s1.Peek(29) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s98(s5, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 202
    * Starting at 0xc94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0xa0d

    requires s0.stack[23] == 0x891

    requires s0.stack[28] == 0x5e4

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa33;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0xa0d;
      assert s1.Peek(23) == 0x891;
      assert s1.Peek(28) == 0x5e4;
      assert s1.Peek(32) == 0x102;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0cae);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s7, gas - 1)
      else
        ExecuteFromCFGNode_s99(s7, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 203
    * Starting at 0xc9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0xa0d

    requires s0.stack[23] == 0x891

    requires s0.stack[28] == 0x5e4

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0xa33;
      assert s1.Peek(13) == 0x997;
      assert s1.Peek(18) == 0xa0d;
      assert s1.Peek(24) == 0x891;
      assert s1.Peek(29) == 0x5e4;
      assert s1.Peek(33) == 0x102;
      var s2 := Dup2(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup6(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0xa33;
      assert s11.Peek(13) == 0x997;
      assert s11.Peek(18) == 0xa0d;
      assert s11.Peek(24) == 0x891;
      assert s11.Peek(29) == 0x5e4;
      assert s11.Peek(33) == 0x102;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x0c94);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s14, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 204
    * Starting at 0xcae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0xa0d

    requires s0.stack[23] == 0x891

    requires s0.stack[28] == 0x5e4

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa33;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0xa0d;
      assert s1.Peek(23) == 0x891;
      assert s1.Peek(28) == 0x5e4;
      assert s1.Peek(32) == 0x102;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap3(s3);
      var s5 := Add(s4);
      var s6 := Swap2(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0xa33;
      assert s11.Peek(9) == 0x997;
      assert s11.Peek(14) == 0xa0d;
      assert s11.Peek(20) == 0x891;
      assert s11.Peek(25) == 0x5e4;
      assert s11.Peek(29) == 0x102;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s13, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 153
    * Starting at 0xa33
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[7] == 0x997

    requires s0.stack[12] == 0xa0d

    requires s0.stack[18] == 0x891

    requires s0.stack[23] == 0x5e4

    requires s0.stack[27] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x997;
      assert s1.Peek(12) == 0xa0d;
      assert s1.Peek(18) == 0x891;
      assert s1.Peek(23) == 0x5e4;
      assert s1.Peek(27) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup7(s9);
      var s11 := Gas(s10);
      assert s11.Peek(14) == 0x997;
      assert s11.Peek(19) == 0xa0d;
      assert s11.Peek(25) == 0x891;
      assert s11.Peek(30) == 0x5e4;
      assert s11.Peek(34) == 0x102;
      var s12 := Call(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := ReturnDataSize(s15);
      var s17 := Dup1(s16);
      var s18 := Push1(s17, 0x00);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x0a70);
      assert s21.Peek(0) == 0xa70;
      assert s21.Peek(10) == 0x997;
      assert s21.Peek(15) == 0xa0d;
      assert s21.Peek(21) == 0x891;
      assert s21.Peek(26) == 0x5e4;
      assert s21.Peek(30) == 0x102;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s117(s22, gas - 1)
      else
        ExecuteFromCFGNode_s102(s22, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 154
    * Starting at 0xa4f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0xa0d

    requires s0.stack[19] == 0x891

    requires s0.stack[24] == 0x5e4

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0xa0d;
      assert s1.Peek(20) == 0x891;
      assert s1.Peek(25) == 0x5e4;
      assert s1.Peek(29) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Push1(s6, 0x3f);
      var s8 := ReturnDataSize(s7);
      var s9 := Add(s8);
      var s10 := And(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(10) == 0x997;
      assert s11.Peek(15) == 0xa0d;
      assert s11.Peek(21) == 0x891;
      assert s11.Peek(26) == 0x5e4;
      assert s11.Peek(30) == 0x102;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(12) == 0x997;
      assert s21.Peek(17) == 0xa0d;
      assert s21.Peek(23) == 0x891;
      assert s21.Peek(28) == 0x5e4;
      assert s21.Peek(32) == 0x102;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x0a75);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s25, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 156
    * Starting at 0xa75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0xa0d

    requires s0.stack[19] == 0x891

    requires s0.stack[24] == 0x5e4

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0xa0d;
      assert s1.Peek(19) == 0x891;
      assert s1.Peek(24) == 0x5e4;
      assert s1.Peek(28) == 0x102;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup2(s6);
      var s8 := Push2(s7, 0x0a86);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s9, gas - 1)
      else
        ExecuteFromCFGNode_s104(s9, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 157
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x997

    requires s0.stack[10] == 0xa0d

    requires s0.stack[16] == 0x891

    requires s0.stack[21] == 0x5e4

    requires s0.stack[25] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x997;
      assert s1.Peek(11) == 0xa0d;
      assert s1.Peek(17) == 0x891;
      assert s1.Peek(22) == 0x5e4;
      assert s1.Peek(26) == 0x102;
      var s2 := Push2(s1, 0x0a0d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s3, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 151
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[6] == 0x997

    requires s0.stack[11] == 0xa0d

    requires s0.stack[17] == 0x891

    requires s0.stack[22] == 0x5e4

    requires s0.stack[26] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x997;
      assert s1.Peek(11) == 0xa0d;
      assert s1.Peek(17) == 0x891;
      assert s1.Peek(22) == 0x5e4;
      assert s1.Peek(26) == 0x102;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s9, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 143
    * Starting at 0x997
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x997 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xa0d

    requires s0.stack[11] == 0x891

    requires s0.stack[16] == 0x5e4

    requires s0.stack[20] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa0d;
      assert s1.Peek(11) == 0x891;
      assert s1.Peek(16) == 0x5e4;
      assert s1.Peek(20) == 0x102;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s8, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 151
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[6] == 0x891

    requires s0.stack[11] == 0x5e4

    requires s0.stack[15] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x891;
      assert s1.Peek(11) == 0x5e4;
      assert s1.Peek(15) == 0x102;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s9, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 158
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x997

    requires s0.stack[10] == 0xa0d

    requires s0.stack[16] == 0x891

    requires s0.stack[21] == 0x5e4

    requires s0.stack[25] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x997;
      assert s1.Peek(10) == 0xa0d;
      assert s1.Peek(16) == 0x891;
      assert s1.Peek(21) == 0x5e4;
      assert s1.Peek(25) == 0x102;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := Push2(s5, 0x0a0d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s7, gas - 1)
      else
        ExecuteFromCFGNode_s109(s7, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 159
    * Starting at 0xa8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[6] == 0x997

    requires s0.stack[11] == 0xa0d

    requires s0.stack[17] == 0x891

    requires s0.stack[22] == 0x5e4

    requires s0.stack[26] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(5) == 0x997;
      assert s1.Peek(10) == 0xa0d;
      assert s1.Peek(16) == 0x891;
      assert s1.Peek(21) == 0x5e4;
      assert s1.Peek(25) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := MLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x0a0d);
      assert s11.Peek(0) == 0xa0d;
      assert s11.Peek(8) == 0x997;
      assert s11.Peek(13) == 0xa0d;
      assert s11.Peek(19) == 0x891;
      assert s11.Peek(24) == 0x5e4;
      assert s11.Peek(28) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0cbc);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s15, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 205
    * Starting at 0xcbc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[2] == 0xa0d

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0xa0d

    requires s0.stack[19] == 0x891

    requires s0.stack[24] == 0x5e4

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa0d;
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0xa0d;
      assert s1.Peek(19) == 0x891;
      assert s1.Peek(24) == 0x5e4;
      assert s1.Peek(28) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0cce);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s112(s10, gas - 1)
      else
        ExecuteFromCFGNode_s111(s10, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 206
    * Starting at 0xcca
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[3] == 0xa0d

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0xa0d

    requires s0.stack[20] == 0x891

    requires s0.stack[25] == 0x5e4

    requires s0.stack[29] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0xa0d;
      assert s1.Peek(10) == 0x997;
      assert s1.Peek(15) == 0xa0d;
      assert s1.Peek(21) == 0x891;
      assert s1.Peek(26) == 0x5e4;
      assert s1.Peek(30) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 112
    * Segment Id for this node is: 207
    * Starting at 0xcce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[3] == 0xa0d

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0xa0d

    requires s0.stack[20] == 0x891

    requires s0.stack[25] == 0x5e4

    requires s0.stack[29] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa0d;
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0xa0d;
      assert s1.Peek(20) == 0x891;
      assert s1.Peek(25) == 0x5e4;
      assert s1.Peek(29) == 0x102;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0b8f);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b2b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s7, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 167
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0xa0d

    requires s0.stack[23] == 0x891

    requires s0.stack[28] == 0x5e4

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0xa0d;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0xa0d;
      assert s1.Peek(23) == 0x891;
      assert s1.Peek(28) == 0x5e4;
      assert s1.Peek(32) == 0x102;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x0780);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s115(s8, gas - 1)
      else
        ExecuteFromCFGNode_s114(s8, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 168
    * Starting at 0xb35
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0xa0d

    requires s0.stack[23] == 0x891

    requires s0.stack[28] == 0x5e4

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb8f;
      assert s1.Peek(7) == 0xa0d;
      assert s1.Peek(13) == 0x997;
      assert s1.Peek(18) == 0xa0d;
      assert s1.Peek(24) == 0x891;
      assert s1.Peek(29) == 0x5e4;
      assert s1.Peek(33) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 115
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0xa0d

    requires s0.stack[23] == 0x891

    requires s0.stack[28] == 0x5e4

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0xa0d;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0xa0d;
      assert s1.Peek(23) == 0x891;
      assert s1.Peek(28) == 0x5e4;
      assert s1.Peek(32) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s3, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 177
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[4] == 0xa0d

    requires s0.stack[10] == 0x997

    requires s0.stack[15] == 0xa0d

    requires s0.stack[21] == 0x891

    requires s0.stack[26] == 0x5e4

    requires s0.stack[30] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa0d;
      assert s1.Peek(10) == 0x997;
      assert s1.Peek(15) == 0xa0d;
      assert s1.Peek(21) == 0x891;
      assert s1.Peek(26) == 0x5e4;
      assert s1.Peek(30) == 0x102;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s7, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 155
    * Starting at 0xa70
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0xa0d

    requires s0.stack[19] == 0x891

    requires s0.stack[24] == 0x5e4

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0xa0d;
      assert s1.Peek(19) == 0x891;
      assert s1.Peek(24) == 0x5e4;
      assert s1.Peek(28) == 0x102;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s103(s4, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 8
    * Starting at 0x59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x8c70830b);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x01bc);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s154(s6, gas - 1)
      else
        ExecuteFromCFGNode_s119(s6, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 9
    * Starting at 0x65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01dc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s5, gas - 1)
      else
        ExecuteFromCFGNode_s120(s5, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 10
    * Starting at 0x70
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa7229fd9);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x020e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s122(s5, gas - 1)
      else
        ExecuteFromCFGNode_s121(s5, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 11
    * Starting at 0x7b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 122
    * Segment Id for this node is: 57
    * Starting at 0x20e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x021a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s124(s6, gas - 1)
      else
        ExecuteFromCFGNode_s123(s6, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 58
    * Starting at 0x216
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x216 as nat
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

  /** Node 124
    * Segment Id for this node is: 59
    * Starting at 0x21a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0102);
      var s4 := Push2(s3, 0x0229);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0bdb);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s8, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 185
    * Starting at 0xbdb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x229

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x229;
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0bf0);
      assert s11.Peek(0) == 0xbf0;
      assert s11.Peek(7) == 0x229;
      assert s11.Peek(8) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s12, gas - 1)
      else
        ExecuteFromCFGNode_s126(s12, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 186
    * Starting at 0xbec
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x229

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x229;
      assert s1.Peek(7) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 127
    * Segment Id for this node is: 187
    * Starting at 0xbf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x229

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x229;
      assert s1.Peek(6) == 0x102;
      var s2 := Dup4(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0bfb);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b16);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s7, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xbfb

    requires s0.stack[8] == 0x229

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbfb;
      assert s1.Peek(8) == 0x229;
      assert s1.Peek(9) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xbfb;
      assert s11.Peek(10) == 0x229;
      assert s11.Peek(11) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s12, gas - 1)
      else
        ExecuteFromCFGNode_s129(s12, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xbfb

    requires s0.stack[8] == 0x229

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xbfb;
      assert s1.Peek(9) == 0x229;
      assert s1.Peek(10) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 130
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xbfb

    requires s0.stack[8] == 0x229

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbfb;
      assert s1.Peek(8) == 0x229;
      assert s1.Peek(9) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s3, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 188
    * Starting at 0xbfb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x229

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x229;
      assert s1.Peek(7) == 0x102;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x0c0b);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x0b16);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s11, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xc0b

    requires s0.stack[8] == 0x229

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc0b;
      assert s1.Peek(8) == 0x229;
      assert s1.Peek(9) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xc0b;
      assert s11.Peek(10) == 0x229;
      assert s11.Peek(11) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s134(s12, gas - 1)
      else
        ExecuteFromCFGNode_s133(s12, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xc0b

    requires s0.stack[8] == 0x229

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xc0b;
      assert s1.Peek(9) == 0x229;
      assert s1.Peek(10) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 134
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xc0b

    requires s0.stack[8] == 0x229

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc0b;
      assert s1.Peek(8) == 0x229;
      assert s1.Peek(9) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s3, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 189
    * Starting at 0xc0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x229

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x229;
      assert s1.Peek(7) == 0x102;
      var s2 := Swap3(s1);
      var s3 := Swap6(s2);
      var s4 := Swap3(s3);
      var s5 := Swap5(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(0) == 0x229;
      assert s11.Peek(5) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s16, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 60
    * Starting at 0x229
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x229 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      var s2 := Push2(s1, 0x04d2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s3, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 102
    * Starting at 0x4d2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x02);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(4) == 0x102;
      var s12 := Push2(s11, 0x04fc);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s13, gas - 1)
      else
        ExecuteFromCFGNode_s138(s13, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 103
    * Starting at 0x4e5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x82b429);
      var s4 := Push1(s3, 0xe8);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(5) == 0x102;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 139
    * Segment Id for this node is: 104
    * Starting at 0x4fc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x102;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Dup4(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0x102;
      var s22 := Push1(s21, 0xff);
      var s23 := And(s22);
      var s24 := Push2(s23, 0x0536);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s25, gas - 1)
      else
        ExecuteFromCFGNode_s140(s25, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 105
    * Starting at 0x51f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x82b429);
      var s4 := Push1(s3, 0xe8);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(6) == 0x102;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 141
    * Segment Id for this node is: 106
    * Starting at 0x536
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xa7229fd900000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(6) == 0x102;
      var s12 := Dup5(s11);
      var s13 := Dup2(s12);
      var s14 := And(s13);
      var s15 := Push1(s14, 0x04);
      var s16 := Dup4(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Address(s18);
      var s20 := Push1(s19, 0x24);
      var s21 := Dup4(s20);
      assert s21.Peek(9) == 0x102;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x44);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := Dup5(s26);
      var s28 := Swap1(s27);
      var s29 := MStore(s28);
      var s30 := Dup6(s29);
      var s31 := And(s30);
      assert s31.Peek(6) == 0x102;
      var s32 := Swap1(s31);
      var s33 := Push4(s32, 0xa7229fd9);
      var s34 := Swap1(s33);
      var s35 := Push1(s34, 0x64);
      var s36 := Add(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Push1(s37, 0x40);
      var s39 := MLoad(s38);
      var s40 := Dup1(s39);
      var s41 := Dup4(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s142(s41, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 107
    * Starting at 0x58d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(10) == 0x102;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup8(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x05a4);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s11, gas - 1)
      else
        ExecuteFromCFGNode_s143(s11, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 108
    * Starting at 0x59b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(9) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 144
    * Segment Id for this node is: 109
    * Starting at 0x5a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Not(s9);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(8) == 0x102;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := And(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Dup1(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(7) == 0x102;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x05c8);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0c74);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s28, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 198
    * Starting at 0xc74
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x5c8

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5c8;
      assert s1.Peek(7) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0c86);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s147(s10, gas - 1)
      else
        ExecuteFromCFGNode_s146(s10, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 199
    * Starting at 0xc82
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5c8

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x5c8;
      assert s1.Peek(9) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 147
    * Segment Id for this node is: 200
    * Starting at 0xc86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5c8

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5c8;
      assert s1.Peek(8) == 0x102;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s7, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 110
    * Starting at 0x5c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s7, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 53
    * Starting at 0x1dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x01e8);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s6, gas - 1)
      else
        ExecuteFromCFGNode_s150(s6, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 54
    * Starting at 0x1e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e4 as nat
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

  /** Node 151
    * Segment Id for this node is: 55
    * Starting at 0x1e8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s152(s10, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 56
    * Starting at 0x1f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0140);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s17, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 34
    * Starting at 0x140
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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

  /** Node 154
    * Segment Id for this node is: 49
    * Starting at 0x1bc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x01c8);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s6, gas - 1)
      else
        ExecuteFromCFGNode_s155(s6, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 50
    * Starting at 0x1c4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c4 as nat
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

  /** Node 156
    * Segment Id for this node is: 51
    * Starting at 0x1c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0102);
      var s4 := Push2(s3, 0x01d7);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0bc2);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s8, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 182
    * Starting at 0xbc2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1d7

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1d7;
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0bd4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s10, gas - 1)
      else
        ExecuteFromCFGNode_s158(s10, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 183
    * Starting at 0xbd0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1d7

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1d7;
      assert s1.Peek(5) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 159
    * Segment Id for this node is: 184
    * Starting at 0xbd4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1d7

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1d7;
      assert s1.Peek(4) == 0x102;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s7, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 52
    * Starting at 0x1d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push2(s1, 0x04c5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s3, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 100
    * Starting at 0x4c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push2(s1, 0x04cd);
      var s3 := Push2(s2, 0x0783);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s4, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 130
    * Starting at 0x783
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x783 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x4cd

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4cd;
      assert s1.Peek(2) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x4cd;
      assert s11.Peek(3) == 0x102;
      var s12 := Push2(s11, 0x04c3);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s13, gas - 1)
      else
        ExecuteFromCFGNode_s163(s13, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 131
    * Starting at 0x796
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x796 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x4cd

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x4cd;
      assert s1.Peek(3) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x4cd;
      assert s11.Peek(6) == 0x102;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(1) == 0x4cd;
      assert s21.Peek(3) == 0x102;
      var s22 := Push1(s21, 0x64);
      var s23 := Add(s22);
      var s24 := Push2(s23, 0x076e);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s25, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 127
    * Starting at 0x76e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x4cd

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4cd;
      assert s1.Peek(3) == 0x102;
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

  /** Node 165
    * Segment Id for this node is: 99
    * Starting at 0x4c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x4cd

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4cd;
      assert s1.Peek(2) == 0x102;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s2, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 101
    * Starting at 0x4cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := SStore(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s4, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 12
    * Starting at 0x7f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x704b6c02);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00b0);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s6, gas - 1)
      else
        ExecuteFromCFGNode_s168(s6, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 13
    * Starting at 0x8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x704b6c02);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0169);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s5, gas - 1)
      else
        ExecuteFromCFGNode_s169(s5, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 14
    * Starting at 0x96
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x715018a6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0189);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s5, gas - 1)
      else
        ExecuteFromCFGNode_s170(s5, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 15
    * Starting at 0xa1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x88543f0e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x019e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s5, gas - 1)
      else
        ExecuteFromCFGNode_s171(s5, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 16
    * Starting at 0xac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 172
    * Segment Id for this node is: 46
    * Starting at 0x19e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x01aa);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s6, gas - 1)
      else
        ExecuteFromCFGNode_s173(s6, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 47
    * Starting at 0x1a6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a6 as nat
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

  /** Node 174
    * Segment Id for this node is: 48
    * Starting at 0x1aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      var s12 := Push2(s11, 0x0140);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s13, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 43
    * Starting at 0x189
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x189 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0195);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s6, gas - 1)
      else
        ExecuteFromCFGNode_s176(s6, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 44
    * Starting at 0x191
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
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

  /** Node 177
    * Segment Id for this node is: 45
    * Starting at 0x195
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x195 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0102);
      var s4 := Push2(s3, 0x04b1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s5, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 97
    * Starting at 0x4b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x102;
      var s2 := Push2(s1, 0x04b9);
      var s3 := Push2(s2, 0x0783);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s4, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 130
    * Starting at 0x783
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x783 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x4b9

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4b9;
      assert s1.Peek(1) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x4b9;
      assert s11.Peek(2) == 0x102;
      var s12 := Push2(s11, 0x04c3);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s13, gas - 1)
      else
        ExecuteFromCFGNode_s180(s13, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 131
    * Starting at 0x796
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x796 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x4b9

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x4b9;
      assert s1.Peek(2) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x4b9;
      assert s11.Peek(5) == 0x102;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(1) == 0x4b9;
      assert s21.Peek(2) == 0x102;
      var s22 := Push1(s21, 0x64);
      var s23 := Add(s22);
      var s24 := Push2(s23, 0x076e);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s25, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 127
    * Starting at 0x76e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x4b9

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b9;
      assert s1.Peek(2) == 0x102;
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

  /** Node 182
    * Segment Id for this node is: 99
    * Starting at 0x4c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x4b9

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4b9;
      assert s1.Peek(1) == 0x102;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s2, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 98
    * Starting at 0x4b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x102;
      var s2 := Push2(s1, 0x04c3);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x081d);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s5, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 136
    * Starting at 0x81d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x4c3

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4c3;
      assert s1.Peek(2) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup4(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x4c3;
      assert s11.Peek(7) == 0x102;
      var s12 := And(s11);
      var s13 := Push32(s12, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000);
      var s14 := Dup4(s13);
      var s15 := And(s14);
      var s16 := Dup2(s15);
      var s17 := Or(s16);
      var s18 := Dup5(s17);
      var s19 := SStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := MLoad(s20);
      assert s21.Peek(6) == 0x4c3;
      assert s21.Peek(7) == 0x102;
      var s22 := Swap2(s21);
      var s23 := Swap1(s22);
      var s24 := Swap3(s23);
      var s25 := And(s24);
      var s26 := Swap3(s25);
      var s27 := Dup4(s26);
      var s28 := Swap2(s27);
      var s29 := Push32(s28, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s30 := Swap2(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x4c3;
      assert s31.Peek(8) == 0x102;
      var s32 := Log3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s35, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 99
    * Starting at 0x4c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x102;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s2, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 39
    * Starting at 0x169
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x169 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0175);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s6, gas - 1)
      else
        ExecuteFromCFGNode_s187(s6, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 40
    * Starting at 0x171
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x171 as nat
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

  /** Node 188
    * Segment Id for this node is: 41
    * Starting at 0x175
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x175 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0102);
      var s4 := Push2(s3, 0x0184);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0b72);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s8, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 174
    * Starting at 0xb72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x184

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x184;
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0b84);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s10, gas - 1)
      else
        ExecuteFromCFGNode_s190(s10, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 175
    * Starting at 0xb80
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x184

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x184;
      assert s1.Peek(5) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 191
    * Segment Id for this node is: 176
    * Starting at 0xb84
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x184

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x184;
      assert s1.Peek(4) == 0x102;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0b8f);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b16);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s7, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x184

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0x184;
      assert s1.Peek(7) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xb8f;
      assert s11.Peek(8) == 0x184;
      assert s11.Peek(9) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s12, gas - 1)
      else
        ExecuteFromCFGNode_s193(s12, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x184

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb8f;
      assert s1.Peek(7) == 0x184;
      assert s1.Peek(8) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 194
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x184

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0x184;
      assert s1.Peek(7) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s3, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 177
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x184

    requires s0.stack[5] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x184;
      assert s1.Peek(5) == 0x102;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s7, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 42
    * Starting at 0x184
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x184 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push2(s1, 0x046f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s3, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 95
    * Starting at 0x46f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push2(s1, 0x0477);
      var s3 := Push2(s2, 0x0783);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s4, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 130
    * Starting at 0x783
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x783 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x477

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x477;
      assert s1.Peek(2) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x477;
      assert s11.Peek(3) == 0x102;
      var s12 := Push2(s11, 0x04c3);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s13, gas - 1)
      else
        ExecuteFromCFGNode_s199(s13, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 131
    * Starting at 0x796
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x796 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x477

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x477;
      assert s1.Peek(3) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x477;
      assert s11.Peek(6) == 0x102;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(1) == 0x477;
      assert s21.Peek(3) == 0x102;
      var s22 := Push1(s21, 0x64);
      var s23 := Add(s22);
      var s24 := Push2(s23, 0x076e);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s25, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 127
    * Starting at 0x76e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x477

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x477;
      assert s1.Peek(3) == 0x102;
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

  /** Node 201
    * Segment Id for this node is: 99
    * Starting at 0x4c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x477

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x477;
      assert s1.Peek(2) == 0x102;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s2, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 96
    * Starting at 0x477
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x477 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push1(s1, 0x02);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000);
      var s6 := And(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(4) == 0x102;
      var s12 := Swap3(s11);
      var s13 := Swap1(s12);
      var s14 := Swap3(s13);
      var s15 := And(s14);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Or(s18);
      var s20 := Swap1(s19);
      var s21 := SStore(s20);
      assert s21.Peek(0) == 0x102;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s22, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 17
    * Starting at 0xb0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x08c4b31f);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00e2);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s337(s6, gas - 1)
      else
        ExecuteFromCFGNode_s204(s6, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 18
    * Starting at 0xbc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x0b7cc33a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0104);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s324(s5, gas - 1)
      else
        ExecuteFromCFGNode_s205(s5, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 19
    * Starting at 0xc7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x6ca4d5a4);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0149);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s207(s5, gas - 1)
      else
        ExecuteFromCFGNode_s206(s5, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 20
    * Starting at 0xd2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 207
    * Segment Id for this node is: 35
    * Starting at 0x149
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0155);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s209(s6, gas - 1)
      else
        ExecuteFromCFGNode_s208(s6, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 36
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
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

  /** Node 209
    * Segment Id for this node is: 37
    * Starting at 0x155
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x155 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0102);
      var s4 := Push2(s3, 0x0164);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0b96);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s8, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 178
    * Starting at 0xb96
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x164

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x164;
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0ba9);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s11, gas - 1)
      else
        ExecuteFromCFGNode_s211(s11, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 179
    * Starting at 0xba5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x164

    requires s0.stack[5] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x164;
      assert s1.Peek(6) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 212
    * Segment Id for this node is: 180
    * Starting at 0xba9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x164

    requires s0.stack[5] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x164;
      assert s1.Peek(5) == 0x102;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0bb4);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b16);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s7, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xbb4

    requires s0.stack[7] == 0x164

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbb4;
      assert s1.Peek(7) == 0x164;
      assert s1.Peek(8) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xbb4;
      assert s11.Peek(9) == 0x164;
      assert s11.Peek(10) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s215(s12, gas - 1)
      else
        ExecuteFromCFGNode_s214(s12, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xbb4

    requires s0.stack[7] == 0x164

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xbb4;
      assert s1.Peek(8) == 0x164;
      assert s1.Peek(9) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 215
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xbb4

    requires s0.stack[7] == 0x164

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbb4;
      assert s1.Peek(7) == 0x164;
      assert s1.Peek(8) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s3, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 181
    * Starting at 0xbb4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x164

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x164;
      assert s1.Peek(6) == 0x102;
      var s2 := Swap5(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap4(s3);
      var s5 := Swap1(s4);
      var s6 := Swap4(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Swap4(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x164;
      assert s11.Peek(4) == 0x102;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s13, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 38
    * Starting at 0x164
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x164 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
      var s2 := Push2(s1, 0x02ff);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s3, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 78
    * Starting at 0x2ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
      var s2 := Push1(s1, 0x02);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(3) == 0x102;
      var s12 := Push2(s11, 0x0329);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s220(s13, gas - 1)
      else
        ExecuteFromCFGNode_s219(s13, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 79
    * Starting at 0x312
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x312 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x82b429);
      var s4 := Push1(s3, 0xe8);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(4) == 0x102;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 220
    * Segment Id for this node is: 80
    * Starting at 0x329
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x329 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x102;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(4) == 0x102;
      var s22 := Push1(s21, 0xff);
      var s23 := And(s22);
      var s24 := Push2(s23, 0x0363);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s222(s25, gas - 1)
      else
        ExecuteFromCFGNode_s221(s25, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 81
    * Starting at 0x34c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x82b429);
      var s4 := Push1(s3, 0xe8);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(5) == 0x102;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 222
    * Segment Id for this node is: 82
    * Starting at 0x363
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x363 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup4(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Dup2(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(8) == 0x102;
      var s12 := Sub(s11);
      var s13 := And(s12);
      var s14 := Push4(s13, 0xfc0c546a);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Dup2(s16);
      var s18 := Push4(s17, 0xffffffff);
      var s19 := And(s18);
      var s20 := Push1(s19, 0xe0);
      var s21 := Shl(s20);
      assert s21.Peek(9) == 0x102;
      var s22 := Dup2(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x04);
      var s25 := Add(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Push1(s26, 0x40);
      var s28 := MLoad(s27);
      var s29 := Dup1(s28);
      var s30 := Dup4(s29);
      var s31 := Sub(s30);
      assert s31.Peek(11) == 0x102;
      var s32 := Dup2(s31);
      var s33 := Dup7(s32);
      var s34 := Gas(s33);
      var s35 := StaticCall(s34);
      var s36 := IsZero(s35);
      var s37 := Dup1(s36);
      var s38 := IsZero(s37);
      var s39 := Push2(s38, 0x03a8);
      var s40 := JumpI(s39);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s39.stack[1] > 0 then
        ExecuteFromCFGNode_s224(s40, gas - 1)
      else
        ExecuteFromCFGNode_s223(s40, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 83
    * Starting at 0x39f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(10) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 224
    * Segment Id for this node is: 84
    * Starting at 0x3a8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Not(s9);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(9) == 0x102;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := And(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Dup1(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(8) == 0x102;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x03cc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0c57);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s28, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 195
    * Starting at 0xc57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x3cc

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3cc;
      assert s1.Peek(8) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0c69);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s227(s10, gas - 1)
      else
        ExecuteFromCFGNode_s226(s10, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 196
    * Starting at 0xc65
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3cc

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x3cc;
      assert s1.Peek(10) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 227
    * Segment Id for this node is: 197
    * Starting at 0xc69
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3cc

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3cc;
      assert s1.Peek(9) == 0x102;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0b8f);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b16);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s7, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x3cc

    requires s0.stack[12] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0x3cc;
      assert s1.Peek(12) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xb8f;
      assert s11.Peek(8) == 0x3cc;
      assert s11.Peek(14) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s12, gas - 1)
      else
        ExecuteFromCFGNode_s229(s12, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x3cc

    requires s0.stack[12] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb8f;
      assert s1.Peek(7) == 0x3cc;
      assert s1.Peek(13) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 230
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x3cc

    requires s0.stack[12] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0x3cc;
      assert s1.Peek(12) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s3, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 177
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3cc

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3cc;
      assert s1.Peek(10) == 0x102;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s7, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 85
    * Starting at 0x3cc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x102;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup3(s9);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x102;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x03ef);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s323(s14, gas - 1)
      else
        ExecuteFromCFGNode_s233(s14, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 86
    * Starting at 0x3e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03ea);
      assert s1.Peek(0) == 0x3ea;
      assert s1.Peek(7) == 0x102;
      var s2 := Dup3(s1);
      var s3 := Dup8(s2);
      var s4 := Dup8(s3);
      var s5 := Push2(s4, 0x07f7);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s6, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 132
    * Starting at 0x7f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x3ea

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ea;
      assert s1.Peek(10) == 0x102;
      var s2 := Push2(s1, 0x0802);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x08cd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s7, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 141
    * Starting at 0x8cd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x802

    requires s0.stack[7] == 0x3ea

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x802;
      assert s1.Peek(7) == 0x3ea;
      assert s1.Peek(14) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x24);
      assert s11.Peek(6) == 0x802;
      assert s11.Peek(10) == 0x3ea;
      assert s11.Peek(17) == 0x102;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x44);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup3(s17);
      var s19 := Swap1(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x802;
      assert s21.Peek(9) == 0x3ea;
      assert s21.Peek(16) == 0x102;
      var s22 := Swap1(s21);
      var s23 := Push2(s22, 0x0997);
      var s24 := Swap1(s23);
      var s25 := Dup6(s24);
      var s26 := Swap1(s25);
      var s27 := Push32(s26, 0x095ea7b300000000000000000000000000000000000000000000000000000000);
      var s28 := Swap1(s27);
      var s29 := Push1(s28, 0x64);
      var s30 := Add(s29);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s236(s30, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 142
    * Starting at 0x915
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x915 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x997

    requires s0.stack[8] == 0x802

    requires s0.stack[12] == 0x3ea

    requires s0.stack[19] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x997;
      assert s1.Peek(8) == 0x802;
      assert s1.Peek(12) == 0x3ea;
      assert s1.Peek(19) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x997;
      assert s11.Peek(10) == 0x802;
      assert s11.Peek(14) == 0x3ea;
      assert s11.Peek(21) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := PushN(s19, 28, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(5) == 0x997;
      assert s21.Peek(10) == 0x802;
      assert s21.Peek(14) == 0x3ea;
      assert s21.Peek(21) == 0x102;
      var s22 := Push32(s21, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := And(s24);
      var s26 := Swap3(s25);
      var s27 := Swap1(s26);
      var s28 := Swap3(s27);
      var s29 := Or(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(4) == 0x997;
      assert s31.Peek(9) == 0x802;
      assert s31.Peek(13) == 0x3ea;
      assert s31.Peek(20) == 0x102;
      var s32 := MStore(s31);
      var s33 := Push2(s32, 0x0a16);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s34, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 152
    * Starting at 0xa16
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x997

    requires s0.stack[7] == 0x802

    requires s0.stack[11] == 0x3ea

    requires s0.stack[18] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x997;
      assert s1.Peek(7) == 0x802;
      assert s1.Peek(11) == 0x3ea;
      assert s1.Peek(18) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x997;
      assert s11.Peek(11) == 0x802;
      assert s11.Peek(15) == 0x3ea;
      assert s11.Peek(22) == 0x102;
      var s12 := Dup5(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0a33);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x0c8d);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s19, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 201
    * Starting at 0xc8d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0xa33

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0x802

    requires s0.stack[18] == 0x3ea

    requires s0.stack[25] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa33;
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0x802;
      assert s1.Peek(18) == 0x3ea;
      assert s1.Peek(25) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s239(s5, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 202
    * Starting at 0xc94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x802

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa33;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x802;
      assert s1.Peek(21) == 0x3ea;
      assert s1.Peek(28) == 0x102;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0cae);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s241(s7, gas - 1)
      else
        ExecuteFromCFGNode_s240(s7, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 203
    * Starting at 0xc9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x802

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0xa33;
      assert s1.Peek(13) == 0x997;
      assert s1.Peek(18) == 0x802;
      assert s1.Peek(22) == 0x3ea;
      assert s1.Peek(29) == 0x102;
      var s2 := Dup2(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup6(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0xa33;
      assert s11.Peek(13) == 0x997;
      assert s11.Peek(18) == 0x802;
      assert s11.Peek(22) == 0x3ea;
      assert s11.Peek(29) == 0x102;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x0c94);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s14, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 204
    * Starting at 0xcae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x802

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa33;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x802;
      assert s1.Peek(21) == 0x3ea;
      assert s1.Peek(28) == 0x102;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap3(s3);
      var s5 := Add(s4);
      var s6 := Swap2(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0xa33;
      assert s11.Peek(9) == 0x997;
      assert s11.Peek(14) == 0x802;
      assert s11.Peek(18) == 0x3ea;
      assert s11.Peek(25) == 0x102;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s13, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 153
    * Starting at 0xa33
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[7] == 0x997

    requires s0.stack[12] == 0x802

    requires s0.stack[16] == 0x3ea

    requires s0.stack[23] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x997;
      assert s1.Peek(12) == 0x802;
      assert s1.Peek(16) == 0x3ea;
      assert s1.Peek(23) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup7(s9);
      var s11 := Gas(s10);
      assert s11.Peek(14) == 0x997;
      assert s11.Peek(19) == 0x802;
      assert s11.Peek(23) == 0x3ea;
      assert s11.Peek(30) == 0x102;
      var s12 := Call(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := ReturnDataSize(s15);
      var s17 := Dup1(s16);
      var s18 := Push1(s17, 0x00);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x0a70);
      assert s21.Peek(0) == 0xa70;
      assert s21.Peek(10) == 0x997;
      assert s21.Peek(15) == 0x802;
      assert s21.Peek(19) == 0x3ea;
      assert s21.Peek(26) == 0x102;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s322(s22, gas - 1)
      else
        ExecuteFromCFGNode_s243(s22, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 154
    * Starting at 0xa4f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x802

    requires s0.stack[17] == 0x3ea

    requires s0.stack[24] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0x802;
      assert s1.Peek(18) == 0x3ea;
      assert s1.Peek(25) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Push1(s6, 0x3f);
      var s8 := ReturnDataSize(s7);
      var s9 := Add(s8);
      var s10 := And(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(10) == 0x997;
      assert s11.Peek(15) == 0x802;
      assert s11.Peek(19) == 0x3ea;
      assert s11.Peek(26) == 0x102;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(12) == 0x997;
      assert s21.Peek(17) == 0x802;
      assert s21.Peek(21) == 0x3ea;
      assert s21.Peek(28) == 0x102;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x0a75);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s25, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 156
    * Starting at 0xa75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x802

    requires s0.stack[17] == 0x3ea

    requires s0.stack[24] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0x802;
      assert s1.Peek(17) == 0x3ea;
      assert s1.Peek(24) == 0x102;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup2(s6);
      var s8 := Push2(s7, 0x0a86);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s313(s9, gas - 1)
      else
        ExecuteFromCFGNode_s245(s9, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 157
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0x997

    requires s0.stack[10] == 0x802

    requires s0.stack[14] == 0x3ea

    requires s0.stack[21] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x997;
      assert s1.Peek(11) == 0x802;
      assert s1.Peek(15) == 0x3ea;
      assert s1.Peek(22) == 0x102;
      var s2 := Push2(s1, 0x0a0d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s3, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 151
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[6] == 0x997

    requires s0.stack[11] == 0x802

    requires s0.stack[15] == 0x3ea

    requires s0.stack[22] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x997;
      assert s1.Peek(11) == 0x802;
      assert s1.Peek(15) == 0x3ea;
      assert s1.Peek(22) == 0x102;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s247(s9, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 143
    * Starting at 0x997
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x997 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x802

    requires s0.stack[9] == 0x3ea

    requires s0.stack[16] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x802;
      assert s1.Peek(9) == 0x3ea;
      assert s1.Peek(16) == 0x102;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s8, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 133
    * Starting at 0x802
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x802 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x3ea

    requires s0.stack[11] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3ea;
      assert s1.Peek(11) == 0x102;
      var s2 := Push2(s1, 0x05e4);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s285(s3, gas - 1)
      else
        ExecuteFromCFGNode_s249(s3, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 134
    * Starting at 0x807
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x807 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x3ea

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0812);
      assert s1.Peek(0) == 0x812;
      assert s1.Peek(4) == 0x3ea;
      assert s1.Peek(11) == 0x102;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push2(s4, 0x099f);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s6, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 144
    * Starting at 0x99f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x812

    requires s0.stack[7] == 0x3ea

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x812;
      assert s1.Peek(7) == 0x3ea;
      assert s1.Peek(14) == 0x102;
      var s2 := Push2(s1, 0x09aa);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x08cd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s7, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 141
    * Starting at 0x8cd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x9aa

    requires s0.stack[7] == 0x812

    requires s0.stack[11] == 0x3ea

    requires s0.stack[18] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9aa;
      assert s1.Peek(7) == 0x812;
      assert s1.Peek(11) == 0x3ea;
      assert s1.Peek(18) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x24);
      assert s11.Peek(6) == 0x9aa;
      assert s11.Peek(10) == 0x812;
      assert s11.Peek(14) == 0x3ea;
      assert s11.Peek(21) == 0x102;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x44);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup3(s17);
      var s19 := Swap1(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x9aa;
      assert s21.Peek(9) == 0x812;
      assert s21.Peek(13) == 0x3ea;
      assert s21.Peek(20) == 0x102;
      var s22 := Swap1(s21);
      var s23 := Push2(s22, 0x0997);
      var s24 := Swap1(s23);
      var s25 := Dup6(s24);
      var s26 := Swap1(s25);
      var s27 := Push32(s26, 0x095ea7b300000000000000000000000000000000000000000000000000000000);
      var s28 := Swap1(s27);
      var s29 := Push1(s28, 0x64);
      var s30 := Add(s29);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s252(s30, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 142
    * Starting at 0x915
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x915 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x997

    requires s0.stack[8] == 0x9aa

    requires s0.stack[12] == 0x812

    requires s0.stack[16] == 0x3ea

    requires s0.stack[23] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x997;
      assert s1.Peek(8) == 0x9aa;
      assert s1.Peek(12) == 0x812;
      assert s1.Peek(16) == 0x3ea;
      assert s1.Peek(23) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x997;
      assert s11.Peek(10) == 0x9aa;
      assert s11.Peek(14) == 0x812;
      assert s11.Peek(18) == 0x3ea;
      assert s11.Peek(25) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := PushN(s19, 28, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(5) == 0x997;
      assert s21.Peek(10) == 0x9aa;
      assert s21.Peek(14) == 0x812;
      assert s21.Peek(18) == 0x3ea;
      assert s21.Peek(25) == 0x102;
      var s22 := Push32(s21, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := And(s24);
      var s26 := Swap3(s25);
      var s27 := Swap1(s26);
      var s28 := Swap3(s27);
      var s29 := Or(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(4) == 0x997;
      assert s31.Peek(9) == 0x9aa;
      assert s31.Peek(13) == 0x812;
      assert s31.Peek(17) == 0x3ea;
      assert s31.Peek(24) == 0x102;
      var s32 := MStore(s31);
      var s33 := Push2(s32, 0x0a16);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s34, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 152
    * Starting at 0xa16
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x997

    requires s0.stack[7] == 0x9aa

    requires s0.stack[11] == 0x812

    requires s0.stack[15] == 0x3ea

    requires s0.stack[22] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x997;
      assert s1.Peek(7) == 0x9aa;
      assert s1.Peek(11) == 0x812;
      assert s1.Peek(15) == 0x3ea;
      assert s1.Peek(22) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x997;
      assert s11.Peek(11) == 0x9aa;
      assert s11.Peek(15) == 0x812;
      assert s11.Peek(19) == 0x3ea;
      assert s11.Peek(26) == 0x102;
      var s12 := Dup5(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0a33);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x0c8d);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s19, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 201
    * Starting at 0xc8d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[2] == 0xa33

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0x9aa

    requires s0.stack[18] == 0x812

    requires s0.stack[22] == 0x3ea

    requires s0.stack[29] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa33;
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0x9aa;
      assert s1.Peek(18) == 0x812;
      assert s1.Peek(22) == 0x3ea;
      assert s1.Peek(29) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s255(s5, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 202
    * Starting at 0xc94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x812

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa33;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x9aa;
      assert s1.Peek(21) == 0x812;
      assert s1.Peek(25) == 0x3ea;
      assert s1.Peek(32) == 0x102;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0cae);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s257(s7, gas - 1)
      else
        ExecuteFromCFGNode_s256(s7, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 203
    * Starting at 0xc9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x812

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0xa33;
      assert s1.Peek(13) == 0x997;
      assert s1.Peek(18) == 0x9aa;
      assert s1.Peek(22) == 0x812;
      assert s1.Peek(26) == 0x3ea;
      assert s1.Peek(33) == 0x102;
      var s2 := Dup2(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup6(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0xa33;
      assert s11.Peek(13) == 0x997;
      assert s11.Peek(18) == 0x9aa;
      assert s11.Peek(22) == 0x812;
      assert s11.Peek(26) == 0x3ea;
      assert s11.Peek(33) == 0x102;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x0c94);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s14, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 204
    * Starting at 0xcae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x812

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa33;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x9aa;
      assert s1.Peek(21) == 0x812;
      assert s1.Peek(25) == 0x3ea;
      assert s1.Peek(32) == 0x102;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap3(s3);
      var s5 := Add(s4);
      var s6 := Swap2(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0xa33;
      assert s11.Peek(9) == 0x997;
      assert s11.Peek(14) == 0x9aa;
      assert s11.Peek(18) == 0x812;
      assert s11.Peek(22) == 0x3ea;
      assert s11.Peek(29) == 0x102;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s258(s13, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 153
    * Starting at 0xa33
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[7] == 0x997

    requires s0.stack[12] == 0x9aa

    requires s0.stack[16] == 0x812

    requires s0.stack[20] == 0x3ea

    requires s0.stack[27] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x997;
      assert s1.Peek(12) == 0x9aa;
      assert s1.Peek(16) == 0x812;
      assert s1.Peek(20) == 0x3ea;
      assert s1.Peek(27) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup7(s9);
      var s11 := Gas(s10);
      assert s11.Peek(14) == 0x997;
      assert s11.Peek(19) == 0x9aa;
      assert s11.Peek(23) == 0x812;
      assert s11.Peek(27) == 0x3ea;
      assert s11.Peek(34) == 0x102;
      var s12 := Call(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := ReturnDataSize(s15);
      var s17 := Dup1(s16);
      var s18 := Push1(s17, 0x00);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x0a70);
      assert s21.Peek(0) == 0xa70;
      assert s21.Peek(10) == 0x997;
      assert s21.Peek(15) == 0x9aa;
      assert s21.Peek(19) == 0x812;
      assert s21.Peek(23) == 0x3ea;
      assert s21.Peek(30) == 0x102;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s312(s22, gas - 1)
      else
        ExecuteFromCFGNode_s259(s22, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 154
    * Starting at 0xa4f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x9aa

    requires s0.stack[17] == 0x812

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0x9aa;
      assert s1.Peek(18) == 0x812;
      assert s1.Peek(22) == 0x3ea;
      assert s1.Peek(29) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Push1(s6, 0x3f);
      var s8 := ReturnDataSize(s7);
      var s9 := Add(s8);
      var s10 := And(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(10) == 0x997;
      assert s11.Peek(15) == 0x9aa;
      assert s11.Peek(19) == 0x812;
      assert s11.Peek(23) == 0x3ea;
      assert s11.Peek(30) == 0x102;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(12) == 0x997;
      assert s21.Peek(17) == 0x9aa;
      assert s21.Peek(21) == 0x812;
      assert s21.Peek(25) == 0x3ea;
      assert s21.Peek(32) == 0x102;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x0a75);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s25, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 156
    * Starting at 0xa75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x9aa

    requires s0.stack[17] == 0x812

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0x9aa;
      assert s1.Peek(17) == 0x812;
      assert s1.Peek(21) == 0x3ea;
      assert s1.Peek(28) == 0x102;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup2(s6);
      var s8 := Push2(s7, 0x0a86);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s303(s9, gas - 1)
      else
        ExecuteFromCFGNode_s261(s9, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 157
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x997

    requires s0.stack[10] == 0x9aa

    requires s0.stack[14] == 0x812

    requires s0.stack[18] == 0x3ea

    requires s0.stack[25] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x997;
      assert s1.Peek(11) == 0x9aa;
      assert s1.Peek(15) == 0x812;
      assert s1.Peek(19) == 0x3ea;
      assert s1.Peek(26) == 0x102;
      var s2 := Push2(s1, 0x0a0d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s3, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 151
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[6] == 0x997

    requires s0.stack[11] == 0x9aa

    requires s0.stack[15] == 0x812

    requires s0.stack[19] == 0x3ea

    requires s0.stack[26] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x997;
      assert s1.Peek(11) == 0x9aa;
      assert s1.Peek(15) == 0x812;
      assert s1.Peek(19) == 0x3ea;
      assert s1.Peek(26) == 0x102;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s263(s9, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 143
    * Starting at 0x997
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x997 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0x9aa

    requires s0.stack[9] == 0x812

    requires s0.stack[13] == 0x3ea

    requires s0.stack[20] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x9aa;
      assert s1.Peek(9) == 0x812;
      assert s1.Peek(13) == 0x3ea;
      assert s1.Peek(20) == 0x102;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s8, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 145
    * Starting at 0x9aa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x812

    requires s0.stack[8] == 0x3ea

    requires s0.stack[15] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x812;
      assert s1.Peek(8) == 0x3ea;
      assert s1.Peek(15) == 0x102;
      var s2 := Push2(s1, 0x05e4);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s266(s3, gas - 1)
      else
        ExecuteFromCFGNode_s265(s3, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 146
    * Starting at 0x9af
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x812

    requires s0.stack[7] == 0x3ea

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x812;
      assert s1.Peek(8) == 0x3ea;
      assert s1.Peek(15) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x73c4154f00000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MLoad(s8);
      var s10 := Dup1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(6) == 0x812;
      assert s11.Peek(10) == 0x3ea;
      assert s11.Peek(17) == 0x102;
      var s12 := Sub(s11);
      var s13 := Swap1(s12);
      var s14 := Revert(s13);
      // Segment is terminal (Revert, Stop or Return)
      s14
  }

  /** Node 266
    * Segment Id for this node is: 113
    * Starting at 0x5e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x812

    requires s0.stack[7] == 0x3ea

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x812;
      assert s1.Peek(7) == 0x3ea;
      assert s1.Peek(14) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s267(s5, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 135
    * Starting at 0x812
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x812 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x3ea

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ea;
      assert s1.Peek(10) == 0x102;
      var s2 := Push2(s1, 0x05e4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x099f);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s7, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 144
    * Starting at 0x99f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x5e4

    requires s0.stack[7] == 0x3ea

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5e4;
      assert s1.Peek(7) == 0x3ea;
      assert s1.Peek(14) == 0x102;
      var s2 := Push2(s1, 0x09aa);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x08cd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s7, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 141
    * Starting at 0x8cd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x9aa

    requires s0.stack[7] == 0x5e4

    requires s0.stack[11] == 0x3ea

    requires s0.stack[18] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9aa;
      assert s1.Peek(7) == 0x5e4;
      assert s1.Peek(11) == 0x3ea;
      assert s1.Peek(18) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x24);
      assert s11.Peek(6) == 0x9aa;
      assert s11.Peek(10) == 0x5e4;
      assert s11.Peek(14) == 0x3ea;
      assert s11.Peek(21) == 0x102;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x44);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup3(s17);
      var s19 := Swap1(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x9aa;
      assert s21.Peek(9) == 0x5e4;
      assert s21.Peek(13) == 0x3ea;
      assert s21.Peek(20) == 0x102;
      var s22 := Swap1(s21);
      var s23 := Push2(s22, 0x0997);
      var s24 := Swap1(s23);
      var s25 := Dup6(s24);
      var s26 := Swap1(s25);
      var s27 := Push32(s26, 0x095ea7b300000000000000000000000000000000000000000000000000000000);
      var s28 := Swap1(s27);
      var s29 := Push1(s28, 0x64);
      var s30 := Add(s29);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s270(s30, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 142
    * Starting at 0x915
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x915 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x997

    requires s0.stack[8] == 0x9aa

    requires s0.stack[12] == 0x5e4

    requires s0.stack[16] == 0x3ea

    requires s0.stack[23] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x997;
      assert s1.Peek(8) == 0x9aa;
      assert s1.Peek(12) == 0x5e4;
      assert s1.Peek(16) == 0x3ea;
      assert s1.Peek(23) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x997;
      assert s11.Peek(10) == 0x9aa;
      assert s11.Peek(14) == 0x5e4;
      assert s11.Peek(18) == 0x3ea;
      assert s11.Peek(25) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := PushN(s19, 28, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(5) == 0x997;
      assert s21.Peek(10) == 0x9aa;
      assert s21.Peek(14) == 0x5e4;
      assert s21.Peek(18) == 0x3ea;
      assert s21.Peek(25) == 0x102;
      var s22 := Push32(s21, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := And(s24);
      var s26 := Swap3(s25);
      var s27 := Swap1(s26);
      var s28 := Swap3(s27);
      var s29 := Or(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(4) == 0x997;
      assert s31.Peek(9) == 0x9aa;
      assert s31.Peek(13) == 0x5e4;
      assert s31.Peek(17) == 0x3ea;
      assert s31.Peek(24) == 0x102;
      var s32 := MStore(s31);
      var s33 := Push2(s32, 0x0a16);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s34, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 152
    * Starting at 0xa16
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x997

    requires s0.stack[7] == 0x9aa

    requires s0.stack[11] == 0x5e4

    requires s0.stack[15] == 0x3ea

    requires s0.stack[22] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x997;
      assert s1.Peek(7) == 0x9aa;
      assert s1.Peek(11) == 0x5e4;
      assert s1.Peek(15) == 0x3ea;
      assert s1.Peek(22) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x997;
      assert s11.Peek(11) == 0x9aa;
      assert s11.Peek(15) == 0x5e4;
      assert s11.Peek(19) == 0x3ea;
      assert s11.Peek(26) == 0x102;
      var s12 := Dup5(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0a33);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x0c8d);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s19, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 201
    * Starting at 0xc8d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[2] == 0xa33

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0x9aa

    requires s0.stack[18] == 0x5e4

    requires s0.stack[22] == 0x3ea

    requires s0.stack[29] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa33;
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0x9aa;
      assert s1.Peek(18) == 0x5e4;
      assert s1.Peek(22) == 0x3ea;
      assert s1.Peek(29) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s273(s5, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 202
    * Starting at 0xc94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x5e4

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa33;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x9aa;
      assert s1.Peek(21) == 0x5e4;
      assert s1.Peek(25) == 0x3ea;
      assert s1.Peek(32) == 0x102;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0cae);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s275(s7, gas - 1)
      else
        ExecuteFromCFGNode_s274(s7, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 203
    * Starting at 0xc9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x5e4

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0xa33;
      assert s1.Peek(13) == 0x997;
      assert s1.Peek(18) == 0x9aa;
      assert s1.Peek(22) == 0x5e4;
      assert s1.Peek(26) == 0x3ea;
      assert s1.Peek(33) == 0x102;
      var s2 := Dup2(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup6(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0xa33;
      assert s11.Peek(13) == 0x997;
      assert s11.Peek(18) == 0x9aa;
      assert s11.Peek(22) == 0x5e4;
      assert s11.Peek(26) == 0x3ea;
      assert s11.Peek(33) == 0x102;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x0c94);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s14, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 204
    * Starting at 0xcae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[5] == 0xa33

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x5e4

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa33;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x9aa;
      assert s1.Peek(21) == 0x5e4;
      assert s1.Peek(25) == 0x3ea;
      assert s1.Peek(32) == 0x102;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap3(s3);
      var s5 := Add(s4);
      var s6 := Swap2(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0xa33;
      assert s11.Peek(9) == 0x997;
      assert s11.Peek(14) == 0x9aa;
      assert s11.Peek(18) == 0x5e4;
      assert s11.Peek(22) == 0x3ea;
      assert s11.Peek(29) == 0x102;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s13, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 153
    * Starting at 0xa33
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[7] == 0x997

    requires s0.stack[12] == 0x9aa

    requires s0.stack[16] == 0x5e4

    requires s0.stack[20] == 0x3ea

    requires s0.stack[27] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x997;
      assert s1.Peek(12) == 0x9aa;
      assert s1.Peek(16) == 0x5e4;
      assert s1.Peek(20) == 0x3ea;
      assert s1.Peek(27) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup7(s9);
      var s11 := Gas(s10);
      assert s11.Peek(14) == 0x997;
      assert s11.Peek(19) == 0x9aa;
      assert s11.Peek(23) == 0x5e4;
      assert s11.Peek(27) == 0x3ea;
      assert s11.Peek(34) == 0x102;
      var s12 := Call(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := ReturnDataSize(s15);
      var s17 := Dup1(s16);
      var s18 := Push1(s17, 0x00);
      var s19 := Dup2(s18);
      var s20 := Eq(s19);
      var s21 := Push2(s20, 0x0a70);
      assert s21.Peek(0) == 0xa70;
      assert s21.Peek(10) == 0x997;
      assert s21.Peek(15) == 0x9aa;
      assert s21.Peek(19) == 0x5e4;
      assert s21.Peek(23) == 0x3ea;
      assert s21.Peek(30) == 0x102;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s302(s22, gas - 1)
      else
        ExecuteFromCFGNode_s277(s22, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 154
    * Starting at 0xa4f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x9aa

    requires s0.stack[17] == 0x5e4

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0x9aa;
      assert s1.Peek(18) == 0x5e4;
      assert s1.Peek(22) == 0x3ea;
      assert s1.Peek(29) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Push1(s6, 0x3f);
      var s8 := ReturnDataSize(s7);
      var s9 := Add(s8);
      var s10 := And(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(10) == 0x997;
      assert s11.Peek(15) == 0x9aa;
      assert s11.Peek(19) == 0x5e4;
      assert s11.Peek(23) == 0x3ea;
      assert s11.Peek(30) == 0x102;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(12) == 0x997;
      assert s21.Peek(17) == 0x9aa;
      assert s21.Peek(21) == 0x5e4;
      assert s21.Peek(25) == 0x3ea;
      assert s21.Peek(32) == 0x102;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x0a75);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s278(s25, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 156
    * Starting at 0xa75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x9aa

    requires s0.stack[17] == 0x5e4

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0x9aa;
      assert s1.Peek(17) == 0x5e4;
      assert s1.Peek(21) == 0x3ea;
      assert s1.Peek(28) == 0x102;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup2(s6);
      var s8 := Push2(s7, 0x0a86);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s293(s9, gas - 1)
      else
        ExecuteFromCFGNode_s279(s9, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 157
    * Starting at 0xa80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x997

    requires s0.stack[10] == 0x9aa

    requires s0.stack[14] == 0x5e4

    requires s0.stack[18] == 0x3ea

    requires s0.stack[25] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x997;
      assert s1.Peek(11) == 0x9aa;
      assert s1.Peek(15) == 0x5e4;
      assert s1.Peek(19) == 0x3ea;
      assert s1.Peek(26) == 0x102;
      var s2 := Push2(s1, 0x0a0d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s3, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 151
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[6] == 0x997

    requires s0.stack[11] == 0x9aa

    requires s0.stack[15] == 0x5e4

    requires s0.stack[19] == 0x3ea

    requires s0.stack[26] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x997;
      assert s1.Peek(11) == 0x9aa;
      assert s1.Peek(15) == 0x5e4;
      assert s1.Peek(19) == 0x3ea;
      assert s1.Peek(26) == 0x102;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s9, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 143
    * Starting at 0x997
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x997 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0x9aa

    requires s0.stack[9] == 0x5e4

    requires s0.stack[13] == 0x3ea

    requires s0.stack[20] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x9aa;
      assert s1.Peek(9) == 0x5e4;
      assert s1.Peek(13) == 0x3ea;
      assert s1.Peek(20) == 0x102;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s8, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 145
    * Starting at 0x9aa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x5e4

    requires s0.stack[8] == 0x3ea

    requires s0.stack[15] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5e4;
      assert s1.Peek(8) == 0x3ea;
      assert s1.Peek(15) == 0x102;
      var s2 := Push2(s1, 0x05e4);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s284(s3, gas - 1)
      else
        ExecuteFromCFGNode_s283(s3, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 146
    * Starting at 0x9af
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x5e4

    requires s0.stack[7] == 0x3ea

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5e4;
      assert s1.Peek(8) == 0x3ea;
      assert s1.Peek(15) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x73c4154f00000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MLoad(s8);
      var s10 := Dup1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(6) == 0x5e4;
      assert s11.Peek(10) == 0x3ea;
      assert s11.Peek(17) == 0x102;
      var s12 := Sub(s11);
      var s13 := Swap1(s12);
      var s14 := Revert(s13);
      // Segment is terminal (Revert, Stop or Return)
      s14
  }

  /** Node 284
    * Segment Id for this node is: 113
    * Starting at 0x5e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x5e4

    requires s0.stack[7] == 0x3ea

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5e4;
      assert s1.Peek(7) == 0x3ea;
      assert s1.Peek(14) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s5, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 113
    * Starting at 0x5e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x3ea

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ea;
      assert s1.Peek(10) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s5, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 87
    * Starting at 0x3ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x102;
      var s2 := Push2(s1, 0x03f2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s287(s3, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 89
    * Starting at 0x3f2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 13
    * Net Stack Effect: +13
    * Net Capacity Effect: -13
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x341a464800000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Dup7(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(9) == 0x102;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Dup5(s17);
      var s19 := And(s18);
      var s20 := Swap1(s19);
      var s21 := Push4(s20, 0x341a4648);
      assert s21.Peek(9) == 0x102;
      var s22 := Swap1(s21);
      var s23 := Dup4(s22);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x00);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(14) == 0x102;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup6(s33);
      var s35 := Dup9(s34);
      var s36 := Dup1(s35);
      var s37 := ExtCodeSize(s36);
      var s38 := IsZero(s37);
      var s39 := Dup1(s38);
      var s40 := IsZero(s39);
      var s41 := Push2(s40, 0x044e);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s288(s41, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 90
    * Starting at 0x449
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x449 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x44e

    requires s0.stack[19] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpI(s0);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s0.stack[1] > 0 then
        ExecuteFromCFGNode_s290(s1, gas - 1)
      else
        ExecuteFromCFGNode_s289(s1, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 91
    * Starting at 0x44a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[17] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(18) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 290
    * Segment Id for this node is: 92
    * Starting at 0x44e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[17] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(17) == 0x102;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0462);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s292(s9, gas - 1)
      else
        ExecuteFromCFGNode_s291(s9, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 93
    * Starting at 0x459
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x459 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(12) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 292
    * Segment Id for this node is: 94
    * Starting at 0x462
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -12
    * Net Capacity Effect: +12
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x462 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x102;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s13, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 158
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x997

    requires s0.stack[10] == 0x9aa

    requires s0.stack[14] == 0x5e4

    requires s0.stack[18] == 0x3ea

    requires s0.stack[25] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x997;
      assert s1.Peek(10) == 0x9aa;
      assert s1.Peek(14) == 0x5e4;
      assert s1.Peek(18) == 0x3ea;
      assert s1.Peek(25) == 0x102;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := Push2(s5, 0x0a0d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s280(s7, gas - 1)
      else
        ExecuteFromCFGNode_s294(s7, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 159
    * Starting at 0xa8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[6] == 0x997

    requires s0.stack[11] == 0x9aa

    requires s0.stack[15] == 0x5e4

    requires s0.stack[19] == 0x3ea

    requires s0.stack[26] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(5) == 0x997;
      assert s1.Peek(10) == 0x9aa;
      assert s1.Peek(14) == 0x5e4;
      assert s1.Peek(18) == 0x3ea;
      assert s1.Peek(25) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := MLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x0a0d);
      assert s11.Peek(0) == 0xa0d;
      assert s11.Peek(8) == 0x997;
      assert s11.Peek(13) == 0x9aa;
      assert s11.Peek(17) == 0x5e4;
      assert s11.Peek(21) == 0x3ea;
      assert s11.Peek(28) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0cbc);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s295(s15, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 205
    * Starting at 0xcbc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[2] == 0xa0d

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x9aa

    requires s0.stack[17] == 0x5e4

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa0d;
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0x9aa;
      assert s1.Peek(17) == 0x5e4;
      assert s1.Peek(21) == 0x3ea;
      assert s1.Peek(28) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0cce);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s297(s10, gas - 1)
      else
        ExecuteFromCFGNode_s296(s10, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 206
    * Starting at 0xcca
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[3] == 0xa0d

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0x9aa

    requires s0.stack[18] == 0x5e4

    requires s0.stack[22] == 0x3ea

    requires s0.stack[29] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0xa0d;
      assert s1.Peek(10) == 0x997;
      assert s1.Peek(15) == 0x9aa;
      assert s1.Peek(19) == 0x5e4;
      assert s1.Peek(23) == 0x3ea;
      assert s1.Peek(30) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 297
    * Segment Id for this node is: 207
    * Starting at 0xcce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[3] == 0xa0d

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0x9aa

    requires s0.stack[18] == 0x5e4

    requires s0.stack[22] == 0x3ea

    requires s0.stack[29] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa0d;
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0x9aa;
      assert s1.Peek(18) == 0x5e4;
      assert s1.Peek(22) == 0x3ea;
      assert s1.Peek(29) == 0x102;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0b8f);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b2b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s298(s7, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 167
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x5e4

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0xa0d;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x9aa;
      assert s1.Peek(21) == 0x5e4;
      assert s1.Peek(25) == 0x3ea;
      assert s1.Peek(32) == 0x102;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x0780);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s300(s8, gas - 1)
      else
        ExecuteFromCFGNode_s299(s8, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 168
    * Starting at 0xb35
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x5e4

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb8f;
      assert s1.Peek(7) == 0xa0d;
      assert s1.Peek(13) == 0x997;
      assert s1.Peek(18) == 0x9aa;
      assert s1.Peek(22) == 0x5e4;
      assert s1.Peek(26) == 0x3ea;
      assert s1.Peek(33) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 300
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x5e4

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0xa0d;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x9aa;
      assert s1.Peek(21) == 0x5e4;
      assert s1.Peek(25) == 0x3ea;
      assert s1.Peek(32) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s301(s3, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 177
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[4] == 0xa0d

    requires s0.stack[10] == 0x997

    requires s0.stack[15] == 0x9aa

    requires s0.stack[19] == 0x5e4

    requires s0.stack[23] == 0x3ea

    requires s0.stack[30] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa0d;
      assert s1.Peek(10) == 0x997;
      assert s1.Peek(15) == 0x9aa;
      assert s1.Peek(19) == 0x5e4;
      assert s1.Peek(23) == 0x3ea;
      assert s1.Peek(30) == 0x102;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s7, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 155
    * Starting at 0xa70
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x9aa

    requires s0.stack[17] == 0x5e4

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0x9aa;
      assert s1.Peek(17) == 0x5e4;
      assert s1.Peek(21) == 0x3ea;
      assert s1.Peek(28) == 0x102;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s278(s4, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 158
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x997

    requires s0.stack[10] == 0x9aa

    requires s0.stack[14] == 0x812

    requires s0.stack[18] == 0x3ea

    requires s0.stack[25] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x997;
      assert s1.Peek(10) == 0x9aa;
      assert s1.Peek(14) == 0x812;
      assert s1.Peek(18) == 0x3ea;
      assert s1.Peek(25) == 0x102;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := Push2(s5, 0x0a0d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s262(s7, gas - 1)
      else
        ExecuteFromCFGNode_s304(s7, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 159
    * Starting at 0xa8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[6] == 0x997

    requires s0.stack[11] == 0x9aa

    requires s0.stack[15] == 0x812

    requires s0.stack[19] == 0x3ea

    requires s0.stack[26] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(5) == 0x997;
      assert s1.Peek(10) == 0x9aa;
      assert s1.Peek(14) == 0x812;
      assert s1.Peek(18) == 0x3ea;
      assert s1.Peek(25) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := MLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x0a0d);
      assert s11.Peek(0) == 0xa0d;
      assert s11.Peek(8) == 0x997;
      assert s11.Peek(13) == 0x9aa;
      assert s11.Peek(17) == 0x812;
      assert s11.Peek(21) == 0x3ea;
      assert s11.Peek(28) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0cbc);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s305(s15, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 205
    * Starting at 0xcbc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[2] == 0xa0d

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x9aa

    requires s0.stack[17] == 0x812

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa0d;
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0x9aa;
      assert s1.Peek(17) == 0x812;
      assert s1.Peek(21) == 0x3ea;
      assert s1.Peek(28) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0cce);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s307(s10, gas - 1)
      else
        ExecuteFromCFGNode_s306(s10, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 206
    * Starting at 0xcca
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[3] == 0xa0d

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0x9aa

    requires s0.stack[18] == 0x812

    requires s0.stack[22] == 0x3ea

    requires s0.stack[29] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0xa0d;
      assert s1.Peek(10) == 0x997;
      assert s1.Peek(15) == 0x9aa;
      assert s1.Peek(19) == 0x812;
      assert s1.Peek(23) == 0x3ea;
      assert s1.Peek(30) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 307
    * Segment Id for this node is: 207
    * Starting at 0xcce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[3] == 0xa0d

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0x9aa

    requires s0.stack[18] == 0x812

    requires s0.stack[22] == 0x3ea

    requires s0.stack[29] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa0d;
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0x9aa;
      assert s1.Peek(18) == 0x812;
      assert s1.Peek(22) == 0x3ea;
      assert s1.Peek(29) == 0x102;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0b8f);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b2b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s7, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 167
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x812

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0xa0d;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x9aa;
      assert s1.Peek(21) == 0x812;
      assert s1.Peek(25) == 0x3ea;
      assert s1.Peek(32) == 0x102;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x0780);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s310(s8, gas - 1)
      else
        ExecuteFromCFGNode_s309(s8, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 168
    * Starting at 0xb35
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x812

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb8f;
      assert s1.Peek(7) == 0xa0d;
      assert s1.Peek(13) == 0x997;
      assert s1.Peek(18) == 0x9aa;
      assert s1.Peek(22) == 0x812;
      assert s1.Peek(26) == 0x3ea;
      assert s1.Peek(33) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 310
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x9aa

    requires s0.stack[21] == 0x812

    requires s0.stack[25] == 0x3ea

    requires s0.stack[32] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0xa0d;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x9aa;
      assert s1.Peek(21) == 0x812;
      assert s1.Peek(25) == 0x3ea;
      assert s1.Peek(32) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s3, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 177
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[4] == 0xa0d

    requires s0.stack[10] == 0x997

    requires s0.stack[15] == 0x9aa

    requires s0.stack[19] == 0x812

    requires s0.stack[23] == 0x3ea

    requires s0.stack[30] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa0d;
      assert s1.Peek(10) == 0x997;
      assert s1.Peek(15) == 0x9aa;
      assert s1.Peek(19) == 0x812;
      assert s1.Peek(23) == 0x3ea;
      assert s1.Peek(30) == 0x102;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s7, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 155
    * Starting at 0xa70
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x9aa

    requires s0.stack[17] == 0x812

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0x9aa;
      assert s1.Peek(17) == 0x812;
      assert s1.Peek(21) == 0x3ea;
      assert s1.Peek(28) == 0x102;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s260(s4, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 158
    * Starting at 0xa86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0x997

    requires s0.stack[10] == 0x802

    requires s0.stack[14] == 0x3ea

    requires s0.stack[21] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x997;
      assert s1.Peek(10) == 0x802;
      assert s1.Peek(14) == 0x3ea;
      assert s1.Peek(21) == 0x102;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := Push2(s5, 0x0a0d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s246(s7, gas - 1)
      else
        ExecuteFromCFGNode_s314(s7, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 159
    * Starting at 0xa8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[6] == 0x997

    requires s0.stack[11] == 0x802

    requires s0.stack[15] == 0x3ea

    requires s0.stack[22] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(5) == 0x997;
      assert s1.Peek(10) == 0x802;
      assert s1.Peek(14) == 0x3ea;
      assert s1.Peek(21) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := MLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x0a0d);
      assert s11.Peek(0) == 0xa0d;
      assert s11.Peek(8) == 0x997;
      assert s11.Peek(13) == 0x802;
      assert s11.Peek(17) == 0x3ea;
      assert s11.Peek(24) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0cbc);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s15, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 205
    * Starting at 0xcbc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[2] == 0xa0d

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x802

    requires s0.stack[17] == 0x3ea

    requires s0.stack[24] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa0d;
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0x802;
      assert s1.Peek(17) == 0x3ea;
      assert s1.Peek(24) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0cce);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s317(s10, gas - 1)
      else
        ExecuteFromCFGNode_s316(s10, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 206
    * Starting at 0xcca
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0xa0d

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0x802

    requires s0.stack[18] == 0x3ea

    requires s0.stack[25] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0xa0d;
      assert s1.Peek(10) == 0x997;
      assert s1.Peek(15) == 0x802;
      assert s1.Peek(19) == 0x3ea;
      assert s1.Peek(26) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 317
    * Segment Id for this node is: 207
    * Starting at 0xcce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0xa0d

    requires s0.stack[9] == 0x997

    requires s0.stack[14] == 0x802

    requires s0.stack[18] == 0x3ea

    requires s0.stack[25] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa0d;
      assert s1.Peek(9) == 0x997;
      assert s1.Peek(14) == 0x802;
      assert s1.Peek(18) == 0x3ea;
      assert s1.Peek(25) == 0x102;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0b8f);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b2b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s318(s7, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 167
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x802

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0xa0d;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x802;
      assert s1.Peek(21) == 0x3ea;
      assert s1.Peek(28) == 0x102;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x0780);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s320(s8, gas - 1)
      else
        ExecuteFromCFGNode_s319(s8, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 168
    * Starting at 0xb35
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x802

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb8f;
      assert s1.Peek(7) == 0xa0d;
      assert s1.Peek(13) == 0x997;
      assert s1.Peek(18) == 0x802;
      assert s1.Peek(22) == 0x3ea;
      assert s1.Peek(29) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 320
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0xa0d

    requires s0.stack[12] == 0x997

    requires s0.stack[17] == 0x802

    requires s0.stack[21] == 0x3ea

    requires s0.stack[28] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0xa0d;
      assert s1.Peek(12) == 0x997;
      assert s1.Peek(17) == 0x802;
      assert s1.Peek(21) == 0x3ea;
      assert s1.Peek(28) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s3, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 177
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[4] == 0xa0d

    requires s0.stack[10] == 0x997

    requires s0.stack[15] == 0x802

    requires s0.stack[19] == 0x3ea

    requires s0.stack[26] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa0d;
      assert s1.Peek(10) == 0x997;
      assert s1.Peek(15) == 0x802;
      assert s1.Peek(19) == 0x3ea;
      assert s1.Peek(26) == 0x102;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s7, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 155
    * Starting at 0xa70
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[8] == 0x997

    requires s0.stack[13] == 0x802

    requires s0.stack[17] == 0x3ea

    requires s0.stack[24] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x997;
      assert s1.Peek(13) == 0x802;
      assert s1.Peek(17) == 0x3ea;
      assert s1.Peek(24) == 0x102;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s244(s4, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 88
    * Starting at 0x3ef
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x102;
      var s2 := Pop(s1);
      var s3 := Dup4(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s287(s3, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 29
    * Starting at 0x104
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0110);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s326(s6, gas - 1)
      else
        ExecuteFromCFGNode_s325(s6, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 30
    * Starting at 0x10c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c as nat
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

  /** Node 326
    * Segment Id for this node is: 31
    * Starting at 0x110
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0134);
      var s4 := Push2(s3, 0x011f);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0b72);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s327(s8, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 174
    * Starting at 0xb72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x11f

    requires s0.stack[3] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11f;
      assert s1.Peek(3) == 0x134;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0b84);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s329(s10, gas - 1)
      else
        ExecuteFromCFGNode_s328(s10, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 175
    * Starting at 0xb80
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x11f

    requires s0.stack[4] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x11f;
      assert s1.Peek(5) == 0x134;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 329
    * Segment Id for this node is: 176
    * Starting at 0xb84
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x11f

    requires s0.stack[4] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11f;
      assert s1.Peek(4) == 0x134;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0b8f);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b16);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s7, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x11f

    requires s0.stack[7] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0x11f;
      assert s1.Peek(7) == 0x134;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xb8f;
      assert s11.Peek(8) == 0x11f;
      assert s11.Peek(9) == 0x134;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s332(s12, gas - 1)
      else
        ExecuteFromCFGNode_s331(s12, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x11f

    requires s0.stack[7] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb8f;
      assert s1.Peek(7) == 0x11f;
      assert s1.Peek(8) == 0x134;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 332
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb8f

    requires s0.stack[6] == 0x11f

    requires s0.stack[7] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb8f;
      assert s1.Peek(6) == 0x11f;
      assert s1.Peek(7) == 0x134;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s333(s3, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 177
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x11f

    requires s0.stack[5] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x11f;
      assert s1.Peek(5) == 0x134;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s334(s7, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 32
    * Starting at 0x11f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x134;
      var s2 := Push1(s1, 0x03);
      var s3 := Push1(s2, 0x20);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Swap1(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x134;
      var s12 := SLoad(s11);
      var s13 := Push1(s12, 0xff);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s16, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 33
    * Starting at 0x134
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x134;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s336(s10, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 34
    * Starting at 0x140
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x134;
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

  /** Node 337
    * Segment Id for this node is: 24
    * Starting at 0xe2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x00ee);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s339(s6, gas - 1)
      else
        ExecuteFromCFGNode_s338(s6, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 25
    * Starting at 0xea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
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

  /** Node 339
    * Segment Id for this node is: 26
    * Starting at 0xee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0102);
      var s4 := Push2(s3, 0x00fd);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0b39);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s340(s8, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 169
    * Starting at 0xb39
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xfd

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfd;
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0b4c);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s342(s11, gas - 1)
      else
        ExecuteFromCFGNode_s341(s11, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 170
    * Starting at 0xb48
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xfd

    requires s0.stack[5] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xfd;
      assert s1.Peek(6) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 342
    * Segment Id for this node is: 171
    * Starting at 0xb4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xfd

    requires s0.stack[5] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xfd;
      assert s1.Peek(5) == 0x102;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0b57);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0b16);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s343(s7, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 165
    * Starting at 0xb16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xb57

    requires s0.stack[7] == 0xfd

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb57;
      assert s1.Peek(7) == 0xfd;
      assert s1.Peek(8) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0780);
      assert s11.Peek(0) == 0x780;
      assert s11.Peek(3) == 0xb57;
      assert s11.Peek(9) == 0xfd;
      assert s11.Peek(10) == 0x102;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s345(s12, gas - 1)
      else
        ExecuteFromCFGNode_s344(s12, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 166
    * Starting at 0xb27
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xb57

    requires s0.stack[7] == 0xfd

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb57;
      assert s1.Peek(8) == 0xfd;
      assert s1.Peek(9) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 345
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xb57

    requires s0.stack[7] == 0xfd

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb57;
      assert s1.Peek(7) == 0xfd;
      assert s1.Peek(8) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s346(s3, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 172
    * Starting at 0xb57
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xfd

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xfd;
      assert s1.Peek(6) == 0x102;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x0b67);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x0b2b);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s11, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 167
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xb67

    requires s0.stack[7] == 0xfd

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb67;
      assert s1.Peek(7) == 0xfd;
      assert s1.Peek(8) == 0x102;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x0780);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s349(s8, gas - 1)
      else
        ExecuteFromCFGNode_s348(s8, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 168
    * Starting at 0xb35
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xb67

    requires s0.stack[7] == 0xfd

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb67;
      assert s1.Peek(8) == 0xfd;
      assert s1.Peek(9) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 349
    * Segment Id for this node is: 129
    * Starting at 0x780
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x780 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xb67

    requires s0.stack[7] == 0xfd

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb67;
      assert s1.Peek(7) == 0xfd;
      assert s1.Peek(8) == 0x102;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s3, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 173
    * Starting at 0xb67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xfd

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xfd;
      assert s1.Peek(6) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Swap3(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s351(s11, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 27
    * Starting at 0xfd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
      var s2 := Push2(s1, 0x02ae);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s3, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 76
    * Starting at 0x2ae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
      var s2 := Push2(s1, 0x02b6);
      var s3 := Push2(s2, 0x0783);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s4, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 130
    * Starting at 0x783
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x783 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x2b6

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2b6;
      assert s1.Peek(3) == 0x102;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x2b6;
      assert s11.Peek(4) == 0x102;
      var s12 := Push2(s11, 0x04c3);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s356(s13, gas - 1)
      else
        ExecuteFromCFGNode_s354(s13, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 131
    * Starting at 0x796
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x796 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x2b6

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x2b6;
      assert s1.Peek(4) == 0x102;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x2b6;
      assert s11.Peek(7) == 0x102;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(1) == 0x2b6;
      assert s21.Peek(4) == 0x102;
      var s22 := Push1(s21, 0x64);
      var s23 := Add(s22);
      var s24 := Push2(s23, 0x076e);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s25, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 127
    * Starting at 0x76e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x2b6

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2b6;
      assert s1.Peek(4) == 0x102;
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

  /** Node 356
    * Segment Id for this node is: 99
    * Starting at 0x4c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x2b6

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2b6;
      assert s1.Peek(3) == 0x102;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s2, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 77
    * Starting at 0x2b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(3) == 0x102;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x03);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap1(s18);
      var s20 := Keccak256(s19);
      var s21 := Dup1(s20);
      assert s21.Peek(3) == 0x102;
      var s22 := SLoad(s21);
      var s23 := Push32(s22, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00);
      var s24 := And(s23);
      var s25 := Swap2(s24);
      var s26 := IsZero(s25);
      var s27 := IsZero(s26);
      var s28 := Swap2(s27);
      var s29 := Swap1(s28);
      var s30 := Swap2(s29);
      var s31 := Or(s30);
      assert s31.Peek(2) == 0x102;
      var s32 := Swap1(s31);
      var s33 := SStore(s32);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s34, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 21
    * Starting at 0xd6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x00dd);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s360(s4, gas - 1)
      else
        ExecuteFromCFGNode_s359(s4, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 22
    * Starting at 0xdc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0);
      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 360
    * Segment Id for this node is: 23
    * Starting at 0xdd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }
}
