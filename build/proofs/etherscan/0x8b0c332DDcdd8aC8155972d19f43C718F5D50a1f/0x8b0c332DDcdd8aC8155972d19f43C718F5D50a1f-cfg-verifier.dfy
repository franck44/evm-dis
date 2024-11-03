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
      var s7 := Push2(s6, 0x0010);
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
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x10
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10 as nat
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
      var s6 := Push2(s5, 0x01c3);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s641(s7, gas - 1)
      else
        ExecuteFromCFGNode_s3(s7, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x1a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a as nat
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
      var s6 := Push4(s5, 0x8c0b5e22);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x00f9);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s367(s9, gas - 1)
      else
        ExecuteFromCFGNode_s4(s9, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xc9567bf9);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0097);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xe95164f5);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0071);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xe95164f5);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x03de);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xef985894);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x03f1);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0404);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x62
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xfcd410be);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0417);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 10
    * Starting at 0x6d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d as nat
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

  /** Node 11
    * Segment Id for this node is: 94
    * Starting at 0x417
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x417 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x08);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0324);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(1) == 0x324;
      var s12 := Dup2(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s13, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 75
    * Starting at 0x324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x324

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x324;
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
      assert s11.Peek(2) == 0x324;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x01f2);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s17, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 51
    * Starting at 0x1f2
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x324

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x324;
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

  /** Node 14
    * Segment Id for this node is: 92
    * Starting at 0x404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01db);
      var s3 := Push2(s2, 0x0412);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1046);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s7, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 228
    * Starting at 0x1046
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1046 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x412

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x412;
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1058);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s10, gas - 1)
      else
        ExecuteFromCFGNode_s16(s10, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 229
    * Starting at 0x1054
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x412

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x412;
      assert s1.Peek(5) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 17
    * Segment Id for this node is: 230
    * Starting at 0x1058
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1058 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x412

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x412;
      assert s1.Peek(4) == 0x1db;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x1063);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s7, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x412

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x412;
      assert s1.Peek(7) == 0x1db;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x1063;
      assert s11.Peek(8) == 0x412;
      assert s11.Peek(9) == 0x1db;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s20(s12, gas - 1)
      else
        ExecuteFromCFGNode_s19(s12, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x412

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(7) == 0x412;
      assert s1.Peek(8) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 20
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x412

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x412;
      assert s1.Peek(7) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s3, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 231
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x412

    requires s0.stack[5] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x412;
      assert s1.Peek(5) == 0x1db;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s7, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 93
    * Starting at 0x412
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x412 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x0a1e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s3, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 165
    * Starting at 0xa1e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x0a26);
      var s3 := Push2(s2, 0x0a94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s4, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 169
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0xa26

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa26;
      assert s1.Peek(2) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0xa26;
      assert s11.Peek(3) == 0x1db;
      var s12 := Push2(s11, 0x060c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s13, gas - 1)
      else
        ExecuteFromCFGNode_s25(s13, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 170
    * Starting at 0xaa7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0xa26

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0xa26;
      assert s1.Peek(3) == 0x1db;
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
      assert s11.Peek(3) == 0xa26;
      assert s11.Peek(5) == 0x1db;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0xa26;
      assert s21.Peek(6) == 0x1db;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x058b);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s27, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0xa26

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa26;
      assert s1.Peek(3) == 0x1db;
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

  /** Node 27
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0xa26

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa26;
      assert s1.Peek(2) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s2, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 166
    * Starting at 0xa26
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0a8b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s10, gas - 1)
      else
        ExecuteFromCFGNode_s29(s10, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 167
    * Starting at 0xa35
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x1db;
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
      assert s11.Peek(4) == 0x1db;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4f776e61626c653a206e6577206f776e657220697320746865207a65726f2061);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0x1db;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x646472657373);
      var s24 := Push1(s23, 0xd0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(2) == 0x1db;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s33, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1db;
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

  /** Node 31
    * Segment Id for this node is: 168
    * Starting at 0xa8b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x08e1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e07);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s5, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 214
    * Starting at 0xe07
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe07 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x8e1

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8e1;
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup4(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x8e1;
      assert s11.Peek(8) == 0x1db;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Not(s17);
      var s19 := Dup4(s18);
      var s20 := And(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(7) == 0x8e1;
      assert s21.Peek(9) == 0x1db;
      var s22 := Or(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Push1(s25, 0x40);
      var s27 := MLoad(s26);
      var s28 := Swap2(s27);
      var s29 := And(s28);
      var s30 := Swap2(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(4) == 0x8e1;
      assert s31.Peek(6) == 0x1db;
      var s32 := Dup3(s31);
      var s33 := Swap1(s32);
      var s34 := Push32(s33, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s35 := Swap1(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Swap1(s36);
      var s38 := Log3(s37);
      var s39 := Pop(s38);
      var s40 := Pop(s39);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s41, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s3, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 48
    * Starting at 0x1db
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1db as nat
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

  /** Node 35
    * Segment Id for this node is: 90
    * Starting at 0x3f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01db);
      var s3 := Push2(s2, 0x03ff);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1125);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s7, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 245
    * Starting at 0x1125
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1125 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x3ff

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3ff;
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1137);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s10, gas - 1)
      else
        ExecuteFromCFGNode_s37(s10, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 246
    * Starting at 0x1133
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x3ff

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x3ff;
      assert s1.Peek(5) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 38
    * Segment Id for this node is: 247
    * Starting at 0x1137
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1137 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x3ff

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ff;
      assert s1.Peek(4) == 0x1db;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s7, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 91
    * Starting at 0x3ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x09d0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s3, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 161
    * Starting at 0x9d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x09d8);
      var s3 := Push2(s2, 0x0a94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s4, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 169
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x9d8

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9d8;
      assert s1.Peek(2) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x9d8;
      assert s11.Peek(3) == 0x1db;
      var s12 := Push2(s11, 0x060c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s44(s13, gas - 1)
      else
        ExecuteFromCFGNode_s42(s13, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 170
    * Starting at 0xaa7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x9d8

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x9d8;
      assert s1.Peek(3) == 0x1db;
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
      assert s11.Peek(3) == 0x9d8;
      assert s11.Peek(5) == 0x1db;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x9d8;
      assert s21.Peek(6) == 0x1db;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x058b);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s27, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x9d8

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9d8;
      assert s1.Peek(3) == 0x1db;
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

  /** Node 44
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x9d8

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9d8;
      assert s1.Peek(2) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s2, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 162
    * Starting at 0x9d8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x0a);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0a14);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s6, gas - 1)
      else
        ExecuteFromCFGNode_s46(s6, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 163
    * Starting at 0x9e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x1db;
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
      assert s11.Peek(4) == 0x1db;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x09);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 9, 0x546178203c20313025);
      var s19 := Push1(s18, 0xb8);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(4) == 0x1db;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x058b);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s28, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 164
    * Starting at 0xa14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x0b);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := SStore(s4);
      var s6 := Push1(s5, 0x0c);
      var s7 := SStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s8, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 88
    * Starting at 0x3de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01db);
      var s3 := Push2(s2, 0x03ec);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1046);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s7, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 228
    * Starting at 0x1046
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1046 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x3ec

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3ec;
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1058);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s10, gas - 1)
      else
        ExecuteFromCFGNode_s50(s10, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 229
    * Starting at 0x1054
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x3ec

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x3ec;
      assert s1.Peek(5) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 51
    * Segment Id for this node is: 230
    * Starting at 0x1058
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1058 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x3ec

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ec;
      assert s1.Peek(4) == 0x1db;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x1063);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s7, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x3ec

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x3ec;
      assert s1.Peek(7) == 0x1db;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x1063;
      assert s11.Peek(8) == 0x3ec;
      assert s11.Peek(9) == 0x1db;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s12, gas - 1)
      else
        ExecuteFromCFGNode_s53(s12, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x3ec

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(7) == 0x3ec;
      assert s1.Peek(8) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 54
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x3ec

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x3ec;
      assert s1.Peek(7) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s3, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 231
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x3ec

    requires s0.stack[5] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3ec;
      assert s1.Peek(5) == 0x1db;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s7, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 89
    * Starting at 0x3ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x08e4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s3, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 151
    * Starting at 0x8e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x08ec);
      var s3 := Push2(s2, 0x0a94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s4, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 169
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x8ec

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8ec;
      assert s1.Peek(2) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x8ec;
      assert s11.Peek(3) == 0x1db;
      var s12 := Push2(s11, 0x060c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s13, gas - 1)
      else
        ExecuteFromCFGNode_s59(s13, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 170
    * Starting at 0xaa7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x8ec

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x8ec;
      assert s1.Peek(3) == 0x1db;
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
      assert s11.Peek(3) == 0x8ec;
      assert s11.Peek(5) == 0x1db;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x8ec;
      assert s21.Peek(6) == 0x1db;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x058b);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s27, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x8ec

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ec;
      assert s1.Peek(3) == 0x1db;
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

  /** Node 61
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x8ec

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8ec;
      assert s1.Peek(2) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s2, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 152
    * Starting at 0x8ec
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x70a08231);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Address(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(5) == 0x1db;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Swap1(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0xa0);
      var s19 := Shl(s18);
      var s20 := Sub(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(5) == 0x1db;
      var s22 := And(s21);
      var s23 := Swap1(s22);
      var s24 := Push4(s23, 0x70a08231);
      var s25 := Swap1(s24);
      var s26 := Push1(s25, 0x24);
      var s27 := Add(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Push1(s28, 0x40);
      var s30 := MLoad(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x1db;
      var s32 := Dup4(s31);
      var s33 := Sub(s32);
      var s34 := Dup2(s33);
      var s35 := Dup7(s34);
      var s36 := Gas(s35);
      var s37 := StaticCall(s36);
      var s38 := IsZero(s37);
      var s39 := Dup1(s38);
      var s40 := IsZero(s39);
      var s41 := Push2(s40, 0x0933);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s63(s41, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 153
    * Starting at 0x929
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x929 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x933

    requires s0.stack[8] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpI(s0);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s0.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s1, gas - 1)
      else
        ExecuteFromCFGNode_s64(s1, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 154
    * Starting at 0x92a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 65
    * Segment Id for this node is: 155
    * Starting at 0x933
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x933 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1db;
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
      assert s11.Peek(6) == 0x1db;
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
      assert s21.Peek(5) == 0x1db;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0957);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1246);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s28, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 272
    * Starting at 0x1246
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1246 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x957

    requires s0.stack[5] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x957;
      assert s1.Peek(5) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1258);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s10, gas - 1)
      else
        ExecuteFromCFGNode_s67(s10, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 273
    * Starting at 0x1254
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1254 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x957

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x957;
      assert s1.Peek(7) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 68
    * Segment Id for this node is: 274
    * Starting at 0x1258
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1258 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x957

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x957;
      assert s1.Peek(6) == 0x1db;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s7, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 156
    * Starting at 0x957
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x957 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0xa9059cbb);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Caller(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(7) == 0x1db;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Dup3(s16);
      var s18 := Swap1(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(4) == 0x1db;
      var s22 := Pop(s21);
      var s23 := Push1(s22, 0x01);
      var s24 := Push1(s23, 0x01);
      var s25 := Push1(s24, 0xa0);
      var s26 := Shl(s25);
      var s27 := Sub(s26);
      var s28 := Dup4(s27);
      var s29 := And(s28);
      var s30 := Swap1(s29);
      var s31 := Push4(s30, 0xa9059cbb);
      assert s31.Peek(5) == 0x1db;
      var s32 := Swap1(s31);
      var s33 := Push1(s32, 0x44);
      var s34 := Add(s33);
      var s35 := Push1(s34, 0x20);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Dup1(s37);
      var s39 := Dup4(s38);
      var s40 := Sub(s39);
      var s41 := Dup2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s70(s41, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 157
    * Starting at 0x992
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x992 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(10) == 0x1db;
      var s2 := Dup8(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x09a7);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s9, gas - 1)
      else
        ExecuteFromCFGNode_s71(s9, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 158
    * Starting at 0x99e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 72
    * Segment Id for this node is: 159
    * Starting at 0x9a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1db;
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
      assert s11.Peek(6) == 0x1db;
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
      assert s21.Peek(5) == 0x1db;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x09cb);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x125f);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s28, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 275
    * Starting at 0x125f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x9cb

    requires s0.stack[5] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9cb;
      assert s1.Peek(5) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1271);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s10, gas - 1)
      else
        ExecuteFromCFGNode_s74(s10, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 276
    * Starting at 0x126d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x9cb

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x9cb;
      assert s1.Peek(7) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 75
    * Segment Id for this node is: 277
    * Starting at 0x1271
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1271 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x9cb

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9cb;
      assert s1.Peek(6) == 0x1db;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x1063);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x113e);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s7, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 248
    * Starting at 0x113e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x9cb

    requires s0.stack[9] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x9cb;
      assert s1.Peek(9) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x08e1);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s8, gas - 1)
      else
        ExecuteFromCFGNode_s77(s8, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 249
    * Starting at 0x1148
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1148 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x9cb

    requires s0.stack[9] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(7) == 0x9cb;
      assert s1.Peek(10) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 78
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x9cb

    requires s0.stack[9] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x9cb;
      assert s1.Peek(9) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s3, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 231
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x9cb

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9cb;
      assert s1.Peek(7) == 0x1db;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s7, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 160
    * Starting at 0x9cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s5, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 11
    * Starting at 0x71
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0xc9567bf9);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0395);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s6, gas - 1)
      else
        ExecuteFromCFGNode_s82(s6, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x039d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s5, gas - 1)
      else
        ExecuteFromCFGNode_s83(s5, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xe086e5ec);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x03d6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s5, gas - 1)
      else
        ExecuteFromCFGNode_s84(s5, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 14
    * Starting at 0x93
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
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

  /** Node 85
    * Segment Id for this node is: 87
    * Starting at 0x3d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01db);
      var s3 := Push2(s2, 0x08ad);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s4, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 147
    * Starting at 0x8ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1db;
      var s2 := Push2(s1, 0x08b5);
      var s3 := Push2(s2, 0x0a94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s4, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 169
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x8b5

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8b5;
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x8b5;
      assert s11.Peek(2) == 0x1db;
      var s12 := Push2(s11, 0x060c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s13, gas - 1)
      else
        ExecuteFromCFGNode_s88(s13, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 170
    * Starting at 0xaa7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x8b5

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x8b5;
      assert s1.Peek(2) == 0x1db;
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
      assert s11.Peek(3) == 0x8b5;
      assert s11.Peek(4) == 0x1db;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x8b5;
      assert s21.Peek(5) == 0x1db;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x058b);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s27, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x8b5

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8b5;
      assert s1.Peek(2) == 0x1db;
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

  /** Node 90
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x8b5

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8b5;
      assert s1.Peek(1) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s2, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 148
    * Starting at 0x8b5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1db;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Caller(s3);
      var s5 := Swap1(s4);
      var s6 := SelfBalance(s5);
      var s7 := Dup1(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x08fc);
      var s10 := Mul(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(4) == 0x1db;
      var s12 := Push1(s11, 0x00);
      var s13 := Dup2(s12);
      var s14 := Dup2(s13);
      var s15 := Dup2(s14);
      var s16 := Dup6(s15);
      var s17 := Dup9(s16);
      var s18 := Dup9(s17);
      var s19 := Call(s18);
      var s20 := Swap4(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0x1db;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := IsZero(s24);
      var s26 := Dup1(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x08e1);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s29, gas - 1)
      else
        ExecuteFromCFGNode_s92(s29, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 149
    * Starting at 0x8d8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(2) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 93
    * Segment Id for this node is: 85
    * Starting at 0x39d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0222);
      var s3 := Push2(s2, 0x03ab);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1185);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s7, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 255
    * Starting at 0x1185
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1185 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x3ab

    requires s0.stack[3] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3ab;
      assert s1.Peek(3) == 0x222;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x1198);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s96(s11, gas - 1)
      else
        ExecuteFromCFGNode_s95(s11, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 256
    * Starting at 0x1194
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1194 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x3ab

    requires s0.stack[5] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x3ab;
      assert s1.Peek(6) == 0x222;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 96
    * Segment Id for this node is: 257
    * Starting at 0x1198
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1198 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x3ab

    requires s0.stack[5] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3ab;
      assert s1.Peek(5) == 0x222;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x11a3);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s7, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x11a3

    requires s0.stack[7] == 0x3ab

    requires s0.stack[8] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11a3;
      assert s1.Peek(7) == 0x3ab;
      assert s1.Peek(8) == 0x222;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x11a3;
      assert s11.Peek(9) == 0x3ab;
      assert s11.Peek(10) == 0x222;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s99(s12, gas - 1)
      else
        ExecuteFromCFGNode_s98(s12, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x11a3

    requires s0.stack[7] == 0x3ab

    requires s0.stack[8] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x11a3;
      assert s1.Peek(8) == 0x3ab;
      assert s1.Peek(9) == 0x222;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 99
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x11a3

    requires s0.stack[7] == 0x3ab

    requires s0.stack[8] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11a3;
      assert s1.Peek(7) == 0x3ab;
      assert s1.Peek(8) == 0x222;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s3, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 258
    * Starting at 0x11a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x3ab

    requires s0.stack[6] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3ab;
      assert s1.Peek(6) == 0x222;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x117a);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x1031);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s11, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x117a

    requires s0.stack[7] == 0x3ab

    requires s0.stack[8] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x117a;
      assert s1.Peek(7) == 0x3ab;
      assert s1.Peek(8) == 0x222;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x117a;
      assert s11.Peek(9) == 0x3ab;
      assert s11.Peek(10) == 0x222;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s12, gas - 1)
      else
        ExecuteFromCFGNode_s102(s12, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x117a

    requires s0.stack[7] == 0x3ab

    requires s0.stack[8] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x117a;
      assert s1.Peek(8) == 0x3ab;
      assert s1.Peek(9) == 0x222;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 103
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x117a

    requires s0.stack[7] == 0x3ab

    requires s0.stack[8] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x117a;
      assert s1.Peek(7) == 0x3ab;
      assert s1.Peek(8) == 0x222;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s3, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 254
    * Starting at 0x117a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x3ab

    requires s0.stack[6] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3ab;
      assert s1.Peek(6) == 0x222;
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
      ExecuteFromCFGNode_s105(s11, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 86
    * Starting at 0x3ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x222;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap2(s6);
      var s8 := Dup3(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x222;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(7) == 0x222;
      var s22 := Keccak256(s21);
      var s23 := Swap4(s22);
      var s24 := Swap1(s23);
      var s25 := Swap5(s24);
      var s26 := And(s25);
      var s27 := Dup3(s26);
      var s28 := MStore(s27);
      var s29 := Swap2(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(4) == 0x222;
      var s32 := MStore(s31);
      var s33 := Keccak256(s32);
      var s34 := SLoad(s33);
      var s35 := Swap1(s34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s36, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 56
    * Starting at 0x222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x01f2);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s10, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 51
    * Starting at 0x1f2
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f2 as nat
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

  /** Node 108
    * Segment Id for this node is: 84
    * Starting at 0x395
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x395 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01db);
      var s3 := Push2(s2, 0x0705);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s4, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 133
    * Starting at 0x705
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x705 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1db;
      var s2 := Push2(s1, 0x070d);
      var s3 := Push2(s2, 0x0a94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s4, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 169
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x70d

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x70d;
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x70d;
      assert s11.Peek(2) == 0x1db;
      var s12 := Push2(s11, 0x060c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s113(s13, gas - 1)
      else
        ExecuteFromCFGNode_s111(s13, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 170
    * Starting at 0xaa7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x70d

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x70d;
      assert s1.Peek(2) == 0x1db;
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
      assert s11.Peek(3) == 0x70d;
      assert s11.Peek(4) == 0x1db;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x70d;
      assert s21.Peek(5) == 0x1db;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x058b);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s27, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x70d

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x70d;
      assert s1.Peek(2) == 0x1db;
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

  /** Node 113
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x70d

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x70d;
      assert s1.Peek(1) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s2, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 134
    * Starting at 0x70d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1db;
      var s2 := Push1(s1, 0x08);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(2) == 0x1db;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := And(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(2) == 0x1db;
      var s22 := And(s21);
      var s23 := Push4(s22, 0xc45a0155);
      var s24 := Push1(s23, 0x40);
      var s25 := MLoad(s24);
      var s26 := Dup2(s25);
      var s27 := Push4(s26, 0xffffffff);
      var s28 := And(s27);
      var s29 := Push1(s28, 0xe0);
      var s30 := Shl(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(5) == 0x1db;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x04);
      var s34 := Add(s33);
      var s35 := Push1(s34, 0x20);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Dup1(s37);
      var s39 := Dup4(s38);
      var s40 := Sub(s39);
      var s41 := Dup2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s115(s41, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 135
    * Starting at 0x74d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup7(s0);
      assert s1.Peek(8) == 0x1db;
      var s2 := Gas(s1);
      var s3 := StaticCall(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0760);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s117(s8, gas - 1)
      else
        ExecuteFromCFGNode_s116(s8, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 136
    * Starting at 0x757
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x757 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(5) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 117
    * Segment Id for this node is: 137
    * Starting at 0x760
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x760 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1db;
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
      assert s11.Peek(4) == 0x1db;
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
      assert s21.Peek(3) == 0x1db;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0784);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1229);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s28, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 269
    * Starting at 0x1229
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1229 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x784

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x784;
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x123b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s120(s10, gas - 1)
      else
        ExecuteFromCFGNode_s119(s10, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 270
    * Starting at 0x1237
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1237 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x784

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x784;
      assert s1.Peek(5) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 120
    * Segment Id for this node is: 271
    * Starting at 0x123b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x784

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x784;
      assert s1.Peek(4) == 0x1db;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x1063);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s7, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x784

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x784;
      assert s1.Peek(7) == 0x1db;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x1063;
      assert s11.Peek(8) == 0x784;
      assert s11.Peek(9) == 0x1db;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s12, gas - 1)
      else
        ExecuteFromCFGNode_s122(s12, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x784

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(7) == 0x784;
      assert s1.Peek(8) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 123
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x784

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x784;
      assert s1.Peek(7) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s3, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 231
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x784

    requires s0.stack[5] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x784;
      assert s1.Peek(5) == 0x1db;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s7, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 138
    * Starting at 0x784
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x784 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push4(s7, 0xe6a43905);
      var s9 := Address(s8);
      var s10 := Push1(s9, 0x08);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x1db;
      var s12 := Swap1(s11);
      var s13 := SLoad(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x0100);
      var s16 := Exp(s15);
      var s17 := Swap1(s16);
      var s18 := Div(s17);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0xa0);
      assert s21.Peek(7) == 0x1db;
      var s22 := Shl(s21);
      var s23 := Sub(s22);
      var s24 := And(s23);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0xa0);
      var s28 := Shl(s27);
      var s29 := Sub(s28);
      var s30 := And(s29);
      var s31 := Push4(s30, 0xad5c4648);
      assert s31.Peek(5) == 0x1db;
      var s32 := Push1(s31, 0x40);
      var s33 := MLoad(s32);
      var s34 := Dup2(s33);
      var s35 := Push4(s34, 0xffffffff);
      var s36 := And(s35);
      var s37 := Push1(s36, 0xe0);
      var s38 := Shl(s37);
      var s39 := Dup2(s38);
      var s40 := MStore(s39);
      var s41 := Push1(s40, 0x04);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s126(s41, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 139
    * Starting at 0x7c9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      assert s1.Peek(6) == 0x1db;
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(7) == 0x1db;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x07e6);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s128(s16, gas - 1)
      else
        ExecuteFromCFGNode_s127(s16, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 140
    * Starting at 0x7dd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(8) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 128
    * Segment Id for this node is: 141
    * Starting at 0x7e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1db;
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
      assert s11.Peek(7) == 0x1db;
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
      assert s21.Peek(6) == 0x1db;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x080a);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1229);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s28, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 269
    * Starting at 0x1229
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1229 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x80a

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x80a;
      assert s1.Peek(6) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x123b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s10, gas - 1)
      else
        ExecuteFromCFGNode_s130(s10, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 270
    * Starting at 0x1237
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1237 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x80a

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x80a;
      assert s1.Peek(8) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 131
    * Segment Id for this node is: 271
    * Starting at 0x123b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x80a

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x80a;
      assert s1.Peek(7) == 0x1db;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x1063);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s7, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x80a

    requires s0.stack[10] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x80a;
      assert s1.Peek(10) == 0x1db;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x1063;
      assert s11.Peek(8) == 0x80a;
      assert s11.Peek(12) == 0x1db;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s134(s12, gas - 1)
      else
        ExecuteFromCFGNode_s133(s12, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x80a

    requires s0.stack[10] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(7) == 0x80a;
      assert s1.Peek(11) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 134
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x80a

    requires s0.stack[10] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x80a;
      assert s1.Peek(10) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s3, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 231
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x80a

    requires s0.stack[8] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x80a;
      assert s1.Peek(8) == 0x1db;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s7, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 142
    * Starting at 0x80a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1db;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xe0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Not(s8);
      var s10 := Push1(s9, 0xe0);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x1db;
      var s12 := Swap1(s11);
      var s13 := Shl(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(6) == 0x1db;
      var s22 := Swap3(s21);
      var s23 := Dup4(s22);
      var s24 := And(s23);
      var s25 := Push1(s24, 0x04);
      var s26 := Dup3(s25);
      var s27 := Add(s26);
      var s28 := MStore(s27);
      var s29 := Swap2(s28);
      var s30 := And(s29);
      var s31 := Push1(s30, 0x24);
      assert s31.Peek(5) == 0x1db;
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x44);
      var s36 := Add(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Push1(s37, 0x40);
      var s39 := MLoad(s38);
      var s40 := Dup1(s39);
      var s41 := Dup4(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s137(s41, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 143
    * Starting at 0x840
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x840 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(6) == 0x1db;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup8(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0857);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s11, gas - 1)
      else
        ExecuteFromCFGNode_s138(s11, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 144
    * Starting at 0x84e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(5) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 139
    * Segment Id for this node is: 145
    * Starting at 0x857
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x857 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1db;
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
      assert s11.Peek(4) == 0x1db;
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
      assert s21.Peek(3) == 0x1db;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x087b);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1229);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s28, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 269
    * Starting at 0x1229
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1229 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x87b

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x87b;
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x123b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s142(s10, gas - 1)
      else
        ExecuteFromCFGNode_s141(s10, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 270
    * Starting at 0x1237
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1237 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x87b

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x87b;
      assert s1.Peek(5) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 142
    * Segment Id for this node is: 271
    * Starting at 0x123b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x87b

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x87b;
      assert s1.Peek(4) == 0x1db;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x1063);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s7, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x87b

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x87b;
      assert s1.Peek(7) == 0x1db;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x1063;
      assert s11.Peek(8) == 0x87b;
      assert s11.Peek(9) == 0x1db;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s12, gas - 1)
      else
        ExecuteFromCFGNode_s144(s12, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x87b

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(7) == 0x87b;
      assert s1.Peek(8) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 145
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x87b

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x87b;
      assert s1.Peek(7) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s3, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 231
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x87b

    requires s0.stack[5] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x87b;
      assert s1.Peek(5) == 0x1db;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s7, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 146
    * Starting at 0x87b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x07);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0xff);
      var s6 := Not(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x1db;
      var s12 := Swap4(s11);
      var s13 := Swap1(s12);
      var s14 := Swap4(s13);
      var s15 := And(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Mul(s16);
      var s18 := Swap3(s17);
      var s19 := Swap1(s18);
      var s20 := Swap3(s19);
      var s21 := And(s20);
      assert s21.Peek(3) == 0x1db;
      var s22 := Push1(s21, 0x01);
      var s23 := Push1(s22, 0x01);
      var s24 := Push1(s23, 0xa8);
      var s25 := Shl(s24);
      var s26 := Sub(s25);
      var s27 := Not(s26);
      var s28 := Swap1(s27);
      var s29 := Swap3(s28);
      var s30 := And(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(3) == 0x1db;
      var s32 := Swap1(s31);
      var s33 := Swap2(s32);
      var s34 := Or(s33);
      var s35 := Push1(s34, 0x01);
      var s36 := Or(s35);
      var s37 := Swap1(s36);
      var s38 := SStore(s37);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s39, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 15
    * Starting at 0x97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0xa10abf3a);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00d3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s333(s6, gas - 1)
      else
        ExecuteFromCFGNode_s149(s6, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 16
    * Starting at 0xa3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa10abf3a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0344);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s314(s5, gas - 1)
      else
        ExecuteFromCFGNode_s150(s5, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 17
    * Starting at 0xae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa457c2d7);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0357);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s288(s5, gas - 1)
      else
        ExecuteFromCFGNode_s151(s5, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 18
    * Starting at 0xb9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa8aa1b31);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x036a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s287(s5, gas - 1)
      else
        ExecuteFromCFGNode_s152(s5, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 19
    * Starting at 0xc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0382);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s154(s5, gas - 1)
      else
        ExecuteFromCFGNode_s153(s5, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 20
    * Starting at 0xcf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf as nat
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

  /** Node 154
    * Segment Id for this node is: 82
    * Starting at 0x382
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x382 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x020e);
      var s3 := Push2(s2, 0x0390);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x10b8);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s7, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 236
    * Starting at 0x10b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x390

    requires s0.stack[3] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x390;
      assert s1.Peek(3) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x10cb);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s157(s11, gas - 1)
      else
        ExecuteFromCFGNode_s156(s11, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 237
    * Starting at 0x10c7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x390

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x390;
      assert s1.Peek(6) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 157
    * Segment Id for this node is: 238
    * Starting at 0x10cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x390

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x390;
      assert s1.Peek(5) == 0x20e;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x10d6);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s7, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x390

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d6;
      assert s1.Peek(7) == 0x390;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x10d6;
      assert s11.Peek(9) == 0x390;
      assert s11.Peek(10) == 0x20e;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s160(s12, gas - 1)
      else
        ExecuteFromCFGNode_s159(s12, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x390

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x10d6;
      assert s1.Peek(8) == 0x390;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 160
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x390

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d6;
      assert s1.Peek(7) == 0x390;
      assert s1.Peek(8) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s3, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 239
    * Starting at 0x10d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x390

    requires s0.stack[6] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x390;
      assert s1.Peek(6) == 0x20e;
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
      assert s11.Peek(1) == 0x390;
      assert s11.Peek(4) == 0x20e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s13, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 83
    * Starting at 0x390
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x390 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20e;
      var s2 := Push2(s1, 0x06f8);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s3, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 132
    * Starting at 0x6f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x04f3);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0c12);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s8, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 177
    * Starting at 0xc12
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc12 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f3;
      assert s1.Peek(7) == 0x20e;
      var s2 := Origin(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x06);
      var s8 := Push1(s7, 0x20);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(5) == 0x4f3;
      assert s11.Peek(9) == 0x20e;
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0xff);
      var s15 := And(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0c35);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s18, gas - 1)
      else
        ExecuteFromCFGNode_s165(s18, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 178
    * Starting at 0xc2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09cb);
      assert s1.Peek(0) == 0x9cb;
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0e59);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s6, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 215
    * Starting at 0xe59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x9cb

    requires s0.stack[7] == 0x4f3

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9cb;
      assert s1.Peek(7) == 0x4f3;
      assert s1.Peek(11) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0ebd);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s10, gas - 1)
      else
        ExecuteFromCFGNode_s167(s10, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 216
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x9cb

    requires s0.stack[7] == 0x4f3

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x9cb;
      assert s1.Peek(8) == 0x4f3;
      assert s1.Peek(12) == 0x20e;
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
      assert s11.Peek(6) == 0x9cb;
      assert s11.Peek(10) == 0x4f3;
      assert s11.Peek(14) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x25);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x9cb;
      assert s21.Peek(10) == 0x4f3;
      assert s21.Peek(14) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 5, 0x6472657373);
      var s24 := Push1(s23, 0xd8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x9cb;
      assert s31.Peek(8) == 0x4f3;
      assert s31.Peek(12) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s33, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x9cb

    requires s0.stack[8] == 0x4f3

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9cb;
      assert s1.Peek(8) == 0x4f3;
      assert s1.Peek(12) == 0x20e;
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

  /** Node 169
    * Segment Id for this node is: 217
    * Starting at 0xebd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x9cb

    requires s0.stack[7] == 0x4f3

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9cb;
      assert s1.Peek(7) == 0x4f3;
      assert s1.Peek(11) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0f1f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s171(s10, gas - 1)
      else
        ExecuteFromCFGNode_s170(s10, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 218
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x9cb

    requires s0.stack[7] == 0x4f3

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x9cb;
      assert s1.Peek(8) == 0x4f3;
      assert s1.Peek(12) == 0x20e;
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
      assert s11.Peek(6) == 0x9cb;
      assert s11.Peek(10) == 0x4f3;
      assert s11.Peek(14) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x23);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x9cb;
      assert s21.Peek(10) == 0x4f3;
      assert s21.Peek(14) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push3(s22, 0x657373);
      var s24 := Push1(s23, 0xe8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x9cb;
      assert s31.Peek(8) == 0x4f3;
      assert s31.Peek(12) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s33, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 219
    * Starting at 0xf1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x9cb

    requires s0.stack[7] == 0x4f3

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9cb;
      assert s1.Peek(7) == 0x4f3;
      assert s1.Peek(11) == 0x20e;
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
      assert s11.Peek(6) == 0x9cb;
      assert s11.Peek(10) == 0x4f3;
      assert s11.Peek(14) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Keccak256(s18);
      var s20 := SLoad(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0x9cb;
      assert s21.Peek(9) == 0x4f3;
      assert s21.Peek(13) == 0x20e;
      var s22 := Dup2(s21);
      var s23 := Lt(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x0f97);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s26, gas - 1)
      else
        ExecuteFromCFGNode_s172(s26, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 220
    * Starting at 0xf41
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x9cb

    requires s0.stack[8] == 0x4f3

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x9cb;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
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
      assert s11.Peek(7) == 0x9cb;
      assert s11.Peek(11) == 0x4f3;
      assert s11.Peek(15) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0x9cb;
      assert s21.Peek(11) == 0x4f3;
      assert s21.Peek(15) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x616c616e6365);
      var s24 := Push1(s23, 0xd0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0x9cb;
      assert s31.Peek(9) == 0x4f3;
      assert s31.Peek(13) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s33, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x9cb

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x9cb;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
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

  /** Node 174
    * Segment Id for this node is: 221
    * Starting at 0xf97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x9cb

    requires s0.stack[8] == 0x4f3

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9cb;
      assert s1.Peek(8) == 0x4f3;
      assert s1.Peek(12) == 0x20e;
      var s2 := Push2(s1, 0x0fa1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1203);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s6, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 265
    * Starting at 0x1203
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xfa1

    requires s0.stack[7] == 0x9cb

    requires s0.stack[11] == 0x4f3

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfa1;
      assert s1.Peek(7) == 0x9cb;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s10, gas - 1)
      else
        ExecuteFromCFGNode_s176(s10, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 266
    * Starting at 0x120f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0x9cb

    requires s0.stack[12] == 0x4f3

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0x9cb;
      assert s1.Peek(13) == 0x4f3;
      assert s1.Peek(17) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s3, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfa1

    requires s0.stack[9] == 0x9cb

    requires s0.stack[13] == 0x4f3

    requires s0.stack[17] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0x9cb;
      assert s1.Peek(13) == 0x4f3;
      assert s1.Peek(17) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfa1;
      assert s11.Peek(11) == 0x9cb;
      assert s11.Peek(15) == 0x4f3;
      assert s11.Peek(19) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 178
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0x9cb

    requires s0.stack[12] == 0x4f3

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfa1;
      assert s1.Peek(8) == 0x9cb;
      assert s1.Peek(12) == 0x4f3;
      assert s1.Peek(16) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s6, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 222
    * Starting at 0xfa1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x9cb

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x9cb;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup7(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x9cb;
      assert s11.Peek(12) == 0x4f3;
      assert s11.Peek(16) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(9) == 0x9cb;
      assert s21.Peek(13) == 0x4f3;
      assert s21.Peek(17) == 0x20e;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap1(s25);
      var s27 := Dup6(s26);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x9cb;
      assert s31.Peek(10) == 0x4f3;
      assert s31.Peek(14) == 0x20e;
      var s32 := Dup2(s31);
      var s33 := Keccak256(s32);
      var s34 := Dup1(s33);
      var s35 := SLoad(s34);
      var s36 := Dup5(s35);
      var s37 := Swap3(s36);
      var s38 := Swap1(s37);
      var s39 := Push2(s38, 0x0fd7);
      var s40 := Swap1(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s180(s41, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 223
    * Starting at 0xfd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0x9cb

    requires s0.stack[14] == 0x4f3

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0x9cb;
      assert s1.Peek(14) == 0x4f3;
      assert s1.Peek(18) == 0x20e;
      var s2 := Push2(s1, 0x1216);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s3, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 267
    * Starting at 0x1216
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0x9cb

    requires s0.stack[14] == 0x4f3

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0x9cb;
      assert s1.Peek(14) == 0x4f3;
      assert s1.Peek(18) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s184(s10, gas - 1)
      else
        ExecuteFromCFGNode_s182(s10, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 268
    * Starting at 0x1222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0x9cb

    requires s0.stack[15] == 0x4f3

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0x9cb;
      assert s1.Peek(16) == 0x4f3;
      assert s1.Peek(20) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s3, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfd7

    requires s0.stack[12] == 0x9cb

    requires s0.stack[16] == 0x4f3

    requires s0.stack[20] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0x9cb;
      assert s1.Peek(16) == 0x4f3;
      assert s1.Peek(20) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfd7;
      assert s11.Peek(14) == 0x9cb;
      assert s11.Peek(18) == 0x4f3;
      assert s11.Peek(22) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 184
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0x9cb

    requires s0.stack[15] == 0x4f3

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfd7;
      assert s1.Peek(11) == 0x9cb;
      assert s1.Peek(15) == 0x4f3;
      assert s1.Peek(19) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s6, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 224
    * Starting at 0xfd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x9cb

    requires s0.stack[12] == 0x4f3

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x9cb;
      assert s1.Peek(12) == 0x4f3;
      assert s1.Peek(16) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0x9cb;
      assert s11.Peek(11) == 0x4f3;
      assert s11.Peek(15) == 0x20e;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(7) == 0x9cb;
      assert s21.Peek(11) == 0x4f3;
      assert s21.Peek(15) == 0x20e;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x1023);
      var s28 := Swap2(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x1023;
      assert s31.Peek(10) == 0x9cb;
      assert s31.Peek(14) == 0x4f3;
      assert s31.Peek(18) == 0x20e;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s34, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 225
    * Starting at 0x1023
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1023 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x9cb

    requires s0.stack[12] == 0x4f3

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x9cb;
      assert s1.Peek(12) == 0x4f3;
      assert s1.Peek(16) == 0x20e;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x9cb;
      assert s11.Peek(5) == 0x4f3;
      assert s11.Peek(9) == 0x20e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s13, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 160
    * Starting at 0x9cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f3;
      assert s1.Peek(7) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s5, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 107
    * Starting at 0x4f3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s189(s3, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s6, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 54
    * Starting at 0x20e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x01f2);
      assert s11.Peek(0) == 0x1f2;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s12, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 179
    * Starting at 0xc35
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f3;
      assert s1.Peek(7) == 0x20e;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := Push2(s5, 0x0c87);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s7, gas - 1)
      else
        ExecuteFromCFGNode_s192(s7, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 180
    * Starting at 0xc40
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc40 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
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
      assert s11.Peek(6) == 0x4f3;
      assert s11.Peek(10) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x547261646520686173206e6f74206265656e206f70656e656420796574000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x4f3;
      assert s21.Peek(10) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x058b);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s26, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4f3

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
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

  /** Node 194
    * Segment Id for this node is: 181
    * Starting at 0xc87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f3;
      assert s1.Peek(7) == 0x20e;
      var s2 := Push1(s1, 0x09);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0c95);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s196(s7, gas - 1)
      else
        ExecuteFromCFGNode_s195(s7, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 182
    * Starting at 0xc91
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 196
    * Segment Id for this node is: 183
    * Starting at 0xc95
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc95 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f3;
      assert s1.Peek(7) == 0x20e;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(7) == 0x4f3;
      assert s11.Peek(11) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := And(s12);
      var s14 := Push2(s13, 0x0100);
      var s15 := Swap1(s14);
      var s16 := Swap3(s15);
      var s17 := Div(s16);
      var s18 := And(s17);
      var s19 := Eq(s18);
      var s20 := Push2(s19, 0x0cb9);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s286(s21, gas - 1)
      else
        ExecuteFromCFGNode_s197(s21, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 184
    * Starting at 0xcb3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4f3

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push2(s1, 0x0cbc);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s3, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 186
    * Starting at 0xcbc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Origin(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x0d);
      var s8 := Push1(s7, 0x20);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(7) == 0x4f3;
      assert s11.Peek(11) == 0x20e;
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Swap1(s13);
      var s15 := Swap2(s14);
      var s16 := Pop(s15);
      var s17 := Push1(s16, 0xff);
      var s18 := And(s17);
      var s19 := Dup1(s18);
      var s20 := IsZero(s19);
      var s21 := Push2(s20, 0x0cf0);
      assert s21.Peek(0) == 0xcf0;
      assert s21.Peek(7) == 0x4f3;
      assert s21.Peek(11) == 0x20e;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s200(s22, gas - 1)
      else
        ExecuteFromCFGNode_s199(s22, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 187
    * Starting at 0xcd9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x4f3;
      assert s11.Peek(11) == 0x20e;
      var s12 := Push2(s11, 0x0100);
      var s13 := Swap1(s12);
      var s14 := Swap3(s13);
      var s15 := Div(s14);
      var s16 := And(s15);
      var s17 := Eq(s16);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s200(s17, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 188
    * Starting at 0xcf0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0cfc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s5, gas - 1)
      else
        ExecuteFromCFGNode_s201(s5, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 189
    * Starting at 0xcf7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := GasPrice(s2);
      var s4 := Gt(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s202(s4, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 190
    * Starting at 0xcfc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0d15);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s5, gas - 1)
      else
        ExecuteFromCFGNode_s203(s5, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 191
    * Starting at 0xd03
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Origin(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Swap1(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(6) == 0x4f3;
      assert s11.Peek(10) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := Keccak256(s12);
      var s14 := SLoad(s13);
      var s15 := Gt(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s204(s15, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 192
    * Starting at 0xd15
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd15 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0d1f);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s4, gas - 1)
      else
        ExecuteFromCFGNode_s205(s4, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 193
    * Starting at 0xd1b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4f3

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 206
    * Segment Id for this node is: 194
    * Starting at 0xd1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4f3

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0d2d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s208(s6, gas - 1)
      else
        ExecuteFromCFGNode_s207(s6, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 195
    * Starting at 0xd27
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x0a);
      var s3 := SLoad(s2);
      var s4 := GasPrice(s3);
      var s5 := Gt(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s208(s5, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 196
    * Starting at 0xd2d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0d37);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s210(s4, gas - 1)
      else
        ExecuteFromCFGNode_s209(s4, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 197
    * Starting at 0xd33
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4f3

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 210
    * Segment Id for this node is: 198
    * Starting at 0xd37
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4f3

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup6(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x4f3;
      assert s11.Peek(11) == 0x20e;
      var s12 := Push2(s11, 0x0100);
      var s13 := Swap1(s12);
      var s14 := Swap3(s13);
      var s15 := Div(s14);
      var s16 := And(s15);
      var s17 := Eq(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Swap1(s19);
      var s21 := Push2(s20, 0x0d6d);
      assert s21.Peek(0) == 0xd6d;
      assert s21.Peek(7) == 0x4f3;
      assert s21.Peek(11) == 0x20e;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s22, gas - 1)
      else
        ExecuteFromCFGNode_s211(s22, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 199
    * Starting at 0xd55
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x4f3;
      assert s11.Peek(11) == 0x20e;
      var s12 := Push2(s11, 0x0100);
      var s13 := Swap1(s12);
      var s14 := Swap3(s13);
      var s15 := Div(s14);
      var s16 := And(s15);
      var s17 := Eq(s16);
      var s18 := IsZero(s17);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s212(s18, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 200
    * Starting at 0xd6d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0d98);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s215(s4, gas - 1)
      else
        ExecuteFromCFGNode_s213(s4, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 201
    * Starting at 0xd73
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4f3

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup5(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x4f3;
      assert s11.Peek(9) == 0x20e;
      var s12 := Push1(s11, 0x0d);
      var s13 := Push1(s12, 0x20);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Swap1(s15);
      var s17 := Keccak256(s16);
      var s18 := SLoad(s17);
      var s19 := Push1(s18, 0xff);
      var s20 := And(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(5) == 0x4f3;
      assert s21.Peek(9) == 0x20e;
      var s22 := Push2(s21, 0x0d98);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s215(s23, gas - 1)
      else
        ExecuteFromCFGNode_s214(s23, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 202
    * Starting at 0xd94
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4f3

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 215
    * Segment Id for this node is: 203
    * Starting at 0xd98
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4f3

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0dbf);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s277(s6, gas - 1)
      else
        ExecuteFromCFGNode_s216(s6, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 204
    * Starting at 0xda1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x0c);
      assert s1.Peek(6) == 0x4f3;
      assert s1.Peek(10) == 0x20e;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x64);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0db0);
      var s6 := Swap1(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x127c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s9, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 278
    * Starting at 0x127c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xdb0

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb0;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0xdb0;
      assert s11.Peek(12) == 0x4f3;
      assert s11.Peek(16) == 0x20e;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x04f7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s220(s14, gas - 1)
      else
        ExecuteFromCFGNode_s218(s14, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 279
    * Starting at 0x128c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdb0

    requires s0.stack[10] == 0x4f3

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdb0;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s3, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xdb0

    requires s0.stack[11] == 0x4f3

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdb0;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xdb0;
      assert s11.Peek(13) == 0x4f3;
      assert s11.Peek(17) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 220
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdb0

    requires s0.stack[10] == 0x4f3

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb0;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s221(s6, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 205
    * Starting at 0xdb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x4f3

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x4f3;
      assert s1.Peek(11) == 0x20e;
      var s2 := Push2(s1, 0x0dba);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x1293);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s6, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 280
    * Starting at 0x1293
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1293 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xdba

    requires s0.stack[8] == 0x4f3

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdba;
      assert s1.Peek(8) == 0x4f3;
      assert s1.Peek(12) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x12b0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s224(s5, gas - 1)
      else
        ExecuteFromCFGNode_s223(s5, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 281
    * Starting at 0x129b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xdba

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0xdba;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x12);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 224
    * Segment Id for this node is: 282
    * Starting at 0x12b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xdba

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdba;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s5, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 206
    * Starting at 0xdba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x4f3

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x4f3;
      assert s1.Peek(10) == 0x20e;
      var s2 := Push2(s1, 0x0dd9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s3, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 209
    * Starting at 0xdd9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x4f3

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x4f3;
      assert s1.Peek(10) == 0x20e;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0def);
      var s5 := Dup6(s4);
      var s6 := Dup6(s5);
      var s7 := Push2(s6, 0x0dea);
      var s8 := Dup5(s7);
      var s9 := Dup8(s8);
      var s10 := Push2(s9, 0x1203);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s11, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 265
    * Starting at 0x1203
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xdea

    requires s0.stack[5] == 0xdef

    requires s0.stack[11] == 0x4f3

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdea;
      assert s1.Peek(5) == 0xdef;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s10, gas - 1)
      else
        ExecuteFromCFGNode_s228(s10, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 266
    * Starting at 0x120f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xdea

    requires s0.stack[6] == 0xdef

    requires s0.stack[12] == 0x4f3

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdea;
      assert s1.Peek(7) == 0xdef;
      assert s1.Peek(13) == 0x4f3;
      assert s1.Peek(17) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s3, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xdea

    requires s0.stack[7] == 0xdef

    requires s0.stack[13] == 0x4f3

    requires s0.stack[17] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdea;
      assert s1.Peek(7) == 0xdef;
      assert s1.Peek(13) == 0x4f3;
      assert s1.Peek(17) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xdea;
      assert s11.Peek(9) == 0xdef;
      assert s11.Peek(15) == 0x4f3;
      assert s11.Peek(19) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 230
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xdea

    requires s0.stack[6] == 0xdef

    requires s0.stack[12] == 0x4f3

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdea;
      assert s1.Peek(6) == 0xdef;
      assert s1.Peek(12) == 0x4f3;
      assert s1.Peek(16) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s6, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 210
    * Starting at 0xdea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdef;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push2(s1, 0x0e59);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s3, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 215
    * Starting at 0xe59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdef;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0ebd);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s235(s10, gas - 1)
      else
        ExecuteFromCFGNode_s233(s10, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 216
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xdef;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
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
      assert s11.Peek(6) == 0xdef;
      assert s11.Peek(12) == 0x4f3;
      assert s11.Peek(16) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x25);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xdef;
      assert s21.Peek(12) == 0x4f3;
      assert s21.Peek(16) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 5, 0x6472657373);
      var s24 := Push1(s23, 0xd8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0xdef;
      assert s31.Peek(10) == 0x4f3;
      assert s31.Peek(14) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s33, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0xdef

    requires s0.stack[10] == 0x4f3

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xdef;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
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

  /** Node 235
    * Segment Id for this node is: 217
    * Starting at 0xebd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdef;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0f1f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s237(s10, gas - 1)
      else
        ExecuteFromCFGNode_s236(s10, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 218
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xdef;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
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
      assert s11.Peek(6) == 0xdef;
      assert s11.Peek(12) == 0x4f3;
      assert s11.Peek(16) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x23);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xdef;
      assert s21.Peek(12) == 0x4f3;
      assert s21.Peek(16) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push3(s22, 0x657373);
      var s24 := Push1(s23, 0xe8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0xdef;
      assert s31.Peek(10) == 0x4f3;
      assert s31.Peek(14) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s33, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 219
    * Starting at 0xf1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdef;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
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
      assert s11.Peek(6) == 0xdef;
      assert s11.Peek(12) == 0x4f3;
      assert s11.Peek(16) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Keccak256(s18);
      var s20 := SLoad(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0xdef;
      assert s21.Peek(11) == 0x4f3;
      assert s21.Peek(15) == 0x20e;
      var s22 := Dup2(s21);
      var s23 := Lt(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x0f97);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s26, gas - 1)
      else
        ExecuteFromCFGNode_s238(s26, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 220
    * Starting at 0xf41
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0xdef

    requires s0.stack[10] == 0x4f3

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0xdef;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
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
      assert s11.Peek(7) == 0xdef;
      assert s11.Peek(13) == 0x4f3;
      assert s11.Peek(17) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0xdef;
      assert s21.Peek(13) == 0x4f3;
      assert s21.Peek(17) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x616c616e6365);
      var s24 := Push1(s23, 0xd0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0xdef;
      assert s31.Peek(11) == 0x4f3;
      assert s31.Peek(15) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s33, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xdef

    requires s0.stack[11] == 0x4f3

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xdef;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
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

  /** Node 240
    * Segment Id for this node is: 221
    * Starting at 0xf97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0xdef

    requires s0.stack[10] == 0x4f3

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xdef;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
      var s2 := Push2(s1, 0x0fa1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1203);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s6, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 265
    * Starting at 0x1203
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xfa1

    requires s0.stack[7] == 0xdef

    requires s0.stack[13] == 0x4f3

    requires s0.stack[17] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfa1;
      assert s1.Peek(7) == 0xdef;
      assert s1.Peek(13) == 0x4f3;
      assert s1.Peek(17) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s244(s10, gas - 1)
      else
        ExecuteFromCFGNode_s242(s10, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 266
    * Starting at 0x120f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0xdef

    requires s0.stack[14] == 0x4f3

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0xdef;
      assert s1.Peek(15) == 0x4f3;
      assert s1.Peek(19) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s3, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfa1

    requires s0.stack[9] == 0xdef

    requires s0.stack[15] == 0x4f3

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0xdef;
      assert s1.Peek(15) == 0x4f3;
      assert s1.Peek(19) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfa1;
      assert s11.Peek(11) == 0xdef;
      assert s11.Peek(17) == 0x4f3;
      assert s11.Peek(21) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 244
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0xdef

    requires s0.stack[14] == 0x4f3

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfa1;
      assert s1.Peek(8) == 0xdef;
      assert s1.Peek(14) == 0x4f3;
      assert s1.Peek(18) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s6, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 222
    * Starting at 0xfa1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xdef

    requires s0.stack[11] == 0x4f3

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xdef;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup7(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0xdef;
      assert s11.Peek(14) == 0x4f3;
      assert s11.Peek(18) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(9) == 0xdef;
      assert s21.Peek(15) == 0x4f3;
      assert s21.Peek(19) == 0x20e;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap1(s25);
      var s27 := Dup6(s26);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0xdef;
      assert s31.Peek(12) == 0x4f3;
      assert s31.Peek(16) == 0x20e;
      var s32 := Dup2(s31);
      var s33 := Keccak256(s32);
      var s34 := Dup1(s33);
      var s35 := SLoad(s34);
      var s36 := Dup5(s35);
      var s37 := Swap3(s36);
      var s38 := Swap1(s37);
      var s39 := Push2(s38, 0x0fd7);
      var s40 := Swap1(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s246(s41, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 223
    * Starting at 0xfd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0xdef

    requires s0.stack[16] == 0x4f3

    requires s0.stack[20] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0xdef;
      assert s1.Peek(16) == 0x4f3;
      assert s1.Peek(20) == 0x20e;
      var s2 := Push2(s1, 0x1216);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s247(s3, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 267
    * Starting at 0x1216
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0xdef

    requires s0.stack[16] == 0x4f3

    requires s0.stack[20] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0xdef;
      assert s1.Peek(16) == 0x4f3;
      assert s1.Peek(20) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s250(s10, gas - 1)
      else
        ExecuteFromCFGNode_s248(s10, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 268
    * Starting at 0x1222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0xdef

    requires s0.stack[17] == 0x4f3

    requires s0.stack[21] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0xdef;
      assert s1.Peek(18) == 0x4f3;
      assert s1.Peek(22) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s3, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfd7

    requires s0.stack[12] == 0xdef

    requires s0.stack[18] == 0x4f3

    requires s0.stack[22] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0xdef;
      assert s1.Peek(18) == 0x4f3;
      assert s1.Peek(22) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfd7;
      assert s11.Peek(14) == 0xdef;
      assert s11.Peek(20) == 0x4f3;
      assert s11.Peek(24) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 250
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0xdef

    requires s0.stack[17] == 0x4f3

    requires s0.stack[21] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfd7;
      assert s1.Peek(11) == 0xdef;
      assert s1.Peek(17) == 0x4f3;
      assert s1.Peek(21) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s6, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 224
    * Starting at 0xfd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0xdef

    requires s0.stack[14] == 0x4f3

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xdef;
      assert s1.Peek(14) == 0x4f3;
      assert s1.Peek(18) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0xdef;
      assert s11.Peek(13) == 0x4f3;
      assert s11.Peek(17) == 0x20e;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(7) == 0xdef;
      assert s21.Peek(13) == 0x4f3;
      assert s21.Peek(17) == 0x20e;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x1023);
      var s28 := Swap2(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x1023;
      assert s31.Peek(10) == 0xdef;
      assert s31.Peek(16) == 0x4f3;
      assert s31.Peek(20) == 0x20e;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s34, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 225
    * Starting at 0x1023
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1023 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0xdef

    requires s0.stack[14] == 0x4f3

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xdef;
      assert s1.Peek(14) == 0x4f3;
      assert s1.Peek(18) == 0x20e;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0xdef;
      assert s11.Peek(7) == 0x4f3;
      assert s11.Peek(11) == 0x20e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s13, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 211
    * Starting at 0xdef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0e00);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s276(s5, gas - 1)
      else
        ExecuteFromCFGNode_s254(s5, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 212
    * Starting at 0xdf6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e00);
      assert s1.Peek(0) == 0xe00;
      assert s1.Peek(6) == 0x4f3;
      assert s1.Peek(10) == 0x20e;
      var s2 := Dup6(s1);
      var s3 := Address(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0e59);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s6, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 215
    * Starting at 0xe59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xe00

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe00;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0ebd);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s258(s10, gas - 1)
      else
        ExecuteFromCFGNode_s256(s10, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 216
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xe00

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xe00;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
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
      assert s11.Peek(6) == 0xe00;
      assert s11.Peek(12) == 0x4f3;
      assert s11.Peek(16) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x25);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xe00;
      assert s21.Peek(12) == 0x4f3;
      assert s21.Peek(16) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 5, 0x6472657373);
      var s24 := Push1(s23, 0xd8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0xe00;
      assert s31.Peek(10) == 0x4f3;
      assert s31.Peek(14) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s33, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0xe00

    requires s0.stack[10] == 0x4f3

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe00;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
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

  /** Node 258
    * Segment Id for this node is: 217
    * Starting at 0xebd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xe00

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe00;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0f1f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s260(s10, gas - 1)
      else
        ExecuteFromCFGNode_s259(s10, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 218
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xe00

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xe00;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
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
      assert s11.Peek(6) == 0xe00;
      assert s11.Peek(12) == 0x4f3;
      assert s11.Peek(16) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x23);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xe00;
      assert s21.Peek(12) == 0x4f3;
      assert s21.Peek(16) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push3(s22, 0x657373);
      var s24 := Push1(s23, 0xe8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0xe00;
      assert s31.Peek(10) == 0x4f3;
      assert s31.Peek(14) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s33, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 219
    * Starting at 0xf1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xe00

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe00;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
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
      assert s11.Peek(6) == 0xe00;
      assert s11.Peek(12) == 0x4f3;
      assert s11.Peek(16) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Keccak256(s18);
      var s20 := SLoad(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0xe00;
      assert s21.Peek(11) == 0x4f3;
      assert s21.Peek(15) == 0x20e;
      var s22 := Dup2(s21);
      var s23 := Lt(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x0f97);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s26, gas - 1)
      else
        ExecuteFromCFGNode_s261(s26, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 220
    * Starting at 0xf41
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0xe00

    requires s0.stack[10] == 0x4f3

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0xe00;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
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
      assert s11.Peek(7) == 0xe00;
      assert s11.Peek(13) == 0x4f3;
      assert s11.Peek(17) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0xe00;
      assert s21.Peek(13) == 0x4f3;
      assert s21.Peek(17) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x616c616e6365);
      var s24 := Push1(s23, 0xd0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0xe00;
      assert s31.Peek(11) == 0x4f3;
      assert s31.Peek(15) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s33, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xe00

    requires s0.stack[11] == 0x4f3

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe00;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
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

  /** Node 263
    * Segment Id for this node is: 221
    * Starting at 0xf97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0xe00

    requires s0.stack[10] == 0x4f3

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe00;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
      var s2 := Push2(s1, 0x0fa1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1203);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s6, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 265
    * Starting at 0x1203
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xfa1

    requires s0.stack[7] == 0xe00

    requires s0.stack[13] == 0x4f3

    requires s0.stack[17] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfa1;
      assert s1.Peek(7) == 0xe00;
      assert s1.Peek(13) == 0x4f3;
      assert s1.Peek(17) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s10, gas - 1)
      else
        ExecuteFromCFGNode_s265(s10, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 266
    * Starting at 0x120f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0xe00

    requires s0.stack[14] == 0x4f3

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0xe00;
      assert s1.Peek(15) == 0x4f3;
      assert s1.Peek(19) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s3, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfa1

    requires s0.stack[9] == 0xe00

    requires s0.stack[15] == 0x4f3

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0xe00;
      assert s1.Peek(15) == 0x4f3;
      assert s1.Peek(19) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfa1;
      assert s11.Peek(11) == 0xe00;
      assert s11.Peek(17) == 0x4f3;
      assert s11.Peek(21) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 267
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0xe00

    requires s0.stack[14] == 0x4f3

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfa1;
      assert s1.Peek(8) == 0xe00;
      assert s1.Peek(14) == 0x4f3;
      assert s1.Peek(18) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s6, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 222
    * Starting at 0xfa1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xe00

    requires s0.stack[11] == 0x4f3

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe00;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup7(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0xe00;
      assert s11.Peek(14) == 0x4f3;
      assert s11.Peek(18) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(9) == 0xe00;
      assert s21.Peek(15) == 0x4f3;
      assert s21.Peek(19) == 0x20e;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap1(s25);
      var s27 := Dup6(s26);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0xe00;
      assert s31.Peek(12) == 0x4f3;
      assert s31.Peek(16) == 0x20e;
      var s32 := Dup2(s31);
      var s33 := Keccak256(s32);
      var s34 := Dup1(s33);
      var s35 := SLoad(s34);
      var s36 := Dup5(s35);
      var s37 := Swap3(s36);
      var s38 := Swap1(s37);
      var s39 := Push2(s38, 0x0fd7);
      var s40 := Swap1(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s269(s41, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 223
    * Starting at 0xfd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0xe00

    requires s0.stack[16] == 0x4f3

    requires s0.stack[20] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0xe00;
      assert s1.Peek(16) == 0x4f3;
      assert s1.Peek(20) == 0x20e;
      var s2 := Push2(s1, 0x1216);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s3, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 267
    * Starting at 0x1216
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0xe00

    requires s0.stack[16] == 0x4f3

    requires s0.stack[20] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0xe00;
      assert s1.Peek(16) == 0x4f3;
      assert s1.Peek(20) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s273(s10, gas - 1)
      else
        ExecuteFromCFGNode_s271(s10, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 268
    * Starting at 0x1222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0xe00

    requires s0.stack[17] == 0x4f3

    requires s0.stack[21] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0xe00;
      assert s1.Peek(18) == 0x4f3;
      assert s1.Peek(22) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s3, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfd7

    requires s0.stack[12] == 0xe00

    requires s0.stack[18] == 0x4f3

    requires s0.stack[22] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0xe00;
      assert s1.Peek(18) == 0x4f3;
      assert s1.Peek(22) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfd7;
      assert s11.Peek(14) == 0xe00;
      assert s11.Peek(20) == 0x4f3;
      assert s11.Peek(24) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 273
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0xe00

    requires s0.stack[17] == 0x4f3

    requires s0.stack[21] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfd7;
      assert s1.Peek(11) == 0xe00;
      assert s1.Peek(17) == 0x4f3;
      assert s1.Peek(21) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s6, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 224
    * Starting at 0xfd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0xe00

    requires s0.stack[14] == 0x4f3

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xe00;
      assert s1.Peek(14) == 0x4f3;
      assert s1.Peek(18) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0xe00;
      assert s11.Peek(13) == 0x4f3;
      assert s11.Peek(17) == 0x20e;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(7) == 0xe00;
      assert s21.Peek(13) == 0x4f3;
      assert s21.Peek(17) == 0x20e;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x1023);
      var s28 := Swap2(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x1023;
      assert s31.Peek(10) == 0xe00;
      assert s31.Peek(16) == 0x4f3;
      assert s31.Peek(20) == 0x20e;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s34, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 225
    * Starting at 0x1023
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1023 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0xe00

    requires s0.stack[14] == 0x4f3

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xe00;
      assert s1.Peek(14) == 0x4f3;
      assert s1.Peek(18) == 0x20e;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0xe00;
      assert s11.Peek(7) == 0x4f3;
      assert s11.Peek(11) == 0x20e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s13, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 213
    * Starting at 0xe00
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s7, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 207
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x0b);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x64);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0dcf);
      var s7 := Swap1(s6);
      var s8 := Dup6(s7);
      var s9 := Push2(s8, 0x127c);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s278(s10, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 278
    * Starting at 0x127c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xdcf

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdcf;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0xdcf;
      assert s11.Peek(12) == 0x4f3;
      assert s11.Peek(16) == 0x20e;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x04f7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s281(s14, gas - 1)
      else
        ExecuteFromCFGNode_s279(s14, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 279
    * Starting at 0x128c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdcf

    requires s0.stack[10] == 0x4f3

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdcf;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s3, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xdcf

    requires s0.stack[11] == 0x4f3

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdcf;
      assert s1.Peek(11) == 0x4f3;
      assert s1.Peek(15) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xdcf;
      assert s11.Peek(13) == 0x4f3;
      assert s11.Peek(17) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 281
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdcf

    requires s0.stack[10] == 0x4f3

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdcf;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s6, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 208
    * Starting at 0xdcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x4f3

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x4f3;
      assert s1.Peek(11) == 0x20e;
      var s2 := Push2(s1, 0x0dd9);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x1293);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s6, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 280
    * Starting at 0x1293
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1293 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xdd9

    requires s0.stack[8] == 0x4f3

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdd9;
      assert s1.Peek(8) == 0x4f3;
      assert s1.Peek(12) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x12b0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s285(s5, gas - 1)
      else
        ExecuteFromCFGNode_s284(s5, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 281
    * Starting at 0x129b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xdd9

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0xdd9;
      assert s1.Peek(10) == 0x4f3;
      assert s1.Peek(14) == 0x20e;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x12);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 285
    * Segment Id for this node is: 282
    * Starting at 0x12b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xdd9

    requires s0.stack[9] == 0x4f3

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdd9;
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s5, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 185
    * Starting at 0xcb9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4f3

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s198(s2, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 81
    * Starting at 0x36a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0324);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Swap1(s6);
      var s8 := Div(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(4) == 0x324;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s16, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 79
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x020e);
      var s3 := Push2(s2, 0x0365);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x10b8);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s7, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 236
    * Starting at 0x10b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x365

    requires s0.stack[3] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x365;
      assert s1.Peek(3) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x10cb);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s291(s11, gas - 1)
      else
        ExecuteFromCFGNode_s290(s11, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 237
    * Starting at 0x10c7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x365

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x365;
      assert s1.Peek(6) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 291
    * Segment Id for this node is: 238
    * Starting at 0x10cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x365

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x365;
      assert s1.Peek(5) == 0x20e;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x10d6);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s7, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x365

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d6;
      assert s1.Peek(7) == 0x365;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x10d6;
      assert s11.Peek(9) == 0x365;
      assert s11.Peek(10) == 0x20e;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s294(s12, gas - 1)
      else
        ExecuteFromCFGNode_s293(s12, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x365

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x10d6;
      assert s1.Peek(8) == 0x365;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 294
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x365

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d6;
      assert s1.Peek(7) == 0x365;
      assert s1.Peek(8) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s295(s3, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 239
    * Starting at 0x10d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x365

    requires s0.stack[6] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x365;
      assert s1.Peek(6) == 0x20e;
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
      assert s11.Peek(1) == 0x365;
      assert s11.Peek(4) == 0x20e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s13, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 80
    * Starting at 0x365
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x365 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20e;
      var s2 := Push2(s1, 0x065d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s297(s3, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 128
    * Starting at 0x65d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20e;
      var s2 := Caller(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x20);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x20e;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup1(s12);
      var s14 := Dup4(s13);
      var s15 := Keccak256(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0xa0);
      var s19 := Shl(s18);
      var s20 := Sub(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(8) == 0x20e;
      var s22 := And(s21);
      var s23 := Dup5(s22);
      var s24 := MStore(s23);
      var s25 := Swap1(s24);
      var s26 := Swap2(s25);
      var s27 := MStore(s26);
      var s28 := Dup2(s27);
      var s29 := Keccak256(s28);
      var s30 := SLoad(s29);
      var s31 := Dup3(s30);
      assert s31.Peek(5) == 0x20e;
      var s32 := Dup2(s31);
      var s33 := Lt(s32);
      var s34 := IsZero(s33);
      var s35 := Push2(s34, 0x06df);
      var s36 := JumpI(s35);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s35.stack[1] > 0 then
        ExecuteFromCFGNode_s300(s36, gas - 1)
      else
        ExecuteFromCFGNode_s298(s36, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 129
    * Starting at 0x68a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x20e;
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
      assert s11.Peek(7) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x25);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a2064656372656173656420616c6c6f77616e63652062656c6f77);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 5, 0x207a65726f);
      var s24 := Push1(s23, 0xd8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s33, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x20e;
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

  /** Node 300
    * Segment Id for this node is: 130
    * Starting at 0x6df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20e;
      var s2 := Push2(s1, 0x06ee);
      var s3 := Caller(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x05a3);
      var s6 := Dup7(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x1203);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s301(s9, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 265
    * Starting at 0x1203
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x5a3

    requires s0.stack[5] == 0x6ee

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a3;
      assert s1.Peek(5) == 0x6ee;
      assert s1.Peek(10) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s304(s10, gas - 1)
      else
        ExecuteFromCFGNode_s302(s10, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 266
    * Starting at 0x120f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x5a3

    requires s0.stack[6] == 0x6ee

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0x5a3;
      assert s1.Peek(7) == 0x6ee;
      assert s1.Peek(12) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s303(s3, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0x5a3

    requires s0.stack[7] == 0x6ee

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0x5a3;
      assert s1.Peek(7) == 0x6ee;
      assert s1.Peek(12) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0x5a3;
      assert s11.Peek(9) == 0x6ee;
      assert s11.Peek(14) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 304
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x5a3

    requires s0.stack[6] == 0x6ee

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a3;
      assert s1.Peek(6) == 0x6ee;
      assert s1.Peek(11) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s305(s6, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 114
    * Starting at 0x5a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x6ee

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6ee;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push2(s1, 0x0aee);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s306(s3, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 171
    * Starting at 0xaee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x6ee

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6ee;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0b50);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s309(s10, gas - 1)
      else
        ExecuteFromCFGNode_s307(s10, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 172
    * Starting at 0xafd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x6ee

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x6ee;
      assert s1.Peek(9) == 0x20e;
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
      assert s11.Peek(6) == 0x6ee;
      assert s11.Peek(11) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup1(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x6ee;
      assert s21.Peek(11) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push4(s22, 0x72657373);
      var s24 := Push1(s23, 0xe0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x6ee;
      assert s31.Peek(9) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s33, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x6ee

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6ee;
      assert s1.Peek(9) == 0x20e;
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

  /** Node 309
    * Segment Id for this node is: 173
    * Starting at 0xb50
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x6ee

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6ee;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0bb1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s311(s10, gas - 1)
      else
        ExecuteFromCFGNode_s310(s10, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 174
    * Starting at 0xb5f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x6ee

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x6ee;
      assert s1.Peek(9) == 0x20e;
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
      assert s11.Peek(6) == 0x6ee;
      assert s11.Peek(11) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x22);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x6ee;
      assert s21.Peek(11) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push2(s22, 0x7373);
      var s24 := Push1(s23, 0xf0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x6ee;
      assert s31.Peek(9) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s33, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 175
    * Starting at 0xbb1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x6ee

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6ee;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x6ee;
      assert s11.Peek(12) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x6ee;
      assert s21.Peek(15) == 0x20e;
      var s22 := Keccak256(s21);
      var s23 := Swap5(s22);
      var s24 := Dup8(s23);
      var s25 := And(s24);
      var s26 := Dup1(s25);
      var s27 := Dup5(s26);
      var s28 := MStore(s27);
      var s29 := Swap5(s28);
      var s30 := Dup3(s29);
      var s31 := MStore(s30);
      assert s31.Peek(8) == 0x6ee;
      assert s31.Peek(13) == 0x20e;
      var s32 := Swap2(s31);
      var s33 := Dup3(s32);
      var s34 := Swap1(s33);
      var s35 := Keccak256(s34);
      var s36 := Dup6(s35);
      var s37 := Swap1(s36);
      var s38 := SStore(s37);
      var s39 := Swap1(s38);
      var s40 := MLoad(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s312(s41, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 176
    * Starting at 0xbe1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x6ee

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x6ee;
      assert s1.Peek(14) == 0x20e;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Swap2(s8);
      var s10 := Sub(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x6ee;
      assert s11.Peek(13) == 0x20e;
      var s12 := Log3(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s313(s16, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 131
    * Starting at 0x6ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap4(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s9, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 77
    * Starting at 0x344
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x344 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01db);
      var s3 := Push2(s2, 0x0352);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x114c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s7, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 250
    * Starting at 0x114c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x352

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x352;
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x115f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s317(s11, gas - 1)
      else
        ExecuteFromCFGNode_s316(s11, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 251
    * Starting at 0x115b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x352

    requires s0.stack[5] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x352;
      assert s1.Peek(6) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 317
    * Segment Id for this node is: 252
    * Starting at 0x115f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x352

    requires s0.stack[5] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x352;
      assert s1.Peek(5) == 0x1db;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x116a);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s318(s7, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x116a

    requires s0.stack[7] == 0x352

    requires s0.stack[8] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116a;
      assert s1.Peek(7) == 0x352;
      assert s1.Peek(8) == 0x1db;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x116a;
      assert s11.Peek(9) == 0x352;
      assert s11.Peek(10) == 0x1db;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s320(s12, gas - 1)
      else
        ExecuteFromCFGNode_s319(s12, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x116a

    requires s0.stack[7] == 0x352

    requires s0.stack[8] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x116a;
      assert s1.Peek(8) == 0x352;
      assert s1.Peek(9) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 320
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x116a

    requires s0.stack[7] == 0x352

    requires s0.stack[8] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116a;
      assert s1.Peek(7) == 0x352;
      assert s1.Peek(8) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s3, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 253
    * Starting at 0x116a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x352

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x352;
      assert s1.Peek(6) == 0x1db;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x117a);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x113e);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s322(s11, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 248
    * Starting at 0x113e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x117a

    requires s0.stack[7] == 0x352

    requires s0.stack[8] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x117a;
      assert s1.Peek(7) == 0x352;
      assert s1.Peek(8) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x08e1);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s324(s8, gas - 1)
      else
        ExecuteFromCFGNode_s323(s8, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 249
    * Starting at 0x1148
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1148 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x117a

    requires s0.stack[7] == 0x352

    requires s0.stack[8] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x117a;
      assert s1.Peek(8) == 0x352;
      assert s1.Peek(9) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 324
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x117a

    requires s0.stack[7] == 0x352

    requires s0.stack[8] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x117a;
      assert s1.Peek(7) == 0x352;
      assert s1.Peek(8) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s325(s3, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 254
    * Starting at 0x117a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x352

    requires s0.stack[6] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x352;
      assert s1.Peek(6) == 0x1db;
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
      ExecuteFromCFGNode_s326(s11, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 78
    * Starting at 0x352
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x352 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1db;
      var s2 := Push2(s1, 0x062a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s327(s3, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 126
    * Starting at 0x62a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1db;
      var s2 := Push2(s1, 0x0632);
      var s3 := Push2(s2, 0x0a94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s4, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 169
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x632

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x632;
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x632;
      assert s11.Peek(4) == 0x1db;
      var s12 := Push2(s11, 0x060c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s331(s13, gas - 1)
      else
        ExecuteFromCFGNode_s329(s13, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 170
    * Starting at 0xaa7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x632

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x632;
      assert s1.Peek(4) == 0x1db;
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
      assert s11.Peek(3) == 0x632;
      assert s11.Peek(6) == 0x1db;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x632;
      assert s21.Peek(7) == 0x1db;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x058b);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s27, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x632

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x632;
      assert s1.Peek(4) == 0x1db;
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

  /** Node 331
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x632

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x632;
      assert s1.Peek(3) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s332(s2, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 127
    * Starting at 0x632
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x632 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1db;
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
      assert s11.Peek(3) == 0x1db;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x0d);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap1(s18);
      var s20 := Keccak256(s19);
      var s21 := Dup1(s20);
      assert s21.Peek(3) == 0x1db;
      var s22 := SLoad(s21);
      var s23 := Push1(s22, 0xff);
      var s24 := Not(s23);
      var s25 := And(s24);
      var s26 := Swap2(s25);
      var s27 := IsZero(s26);
      var s28 := IsZero(s27);
      var s29 := Swap2(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(3) == 0x1db;
      var s32 := Or(s31);
      var s33 := Swap1(s32);
      var s34 := SStore(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s35, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 21
    * Starting at 0xd3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x8c0b5e22);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x030e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s364(s6, gas - 1)
      else
        ExecuteFromCFGNode_s334(s6, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 22
    * Starting at 0xdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0317);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s362(s5, gas - 1)
      else
        ExecuteFromCFGNode_s335(s5, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 23
    * Starting at 0xea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x033c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s337(s5, gas - 1)
      else
        ExecuteFromCFGNode_s336(s5, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 24
    * Starting at 0xf5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5 as nat
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

  /** Node 337
    * Segment Id for this node is: 76
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e5);
      var s3 := Push2(s2, 0x061b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s338(s4, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 125
    * Starting at 0x61b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e5;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x0463);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x11b3);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s9, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 259
    * Starting at 0x11b3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x463

    requires s0.stack[4] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x463;
      assert s1.Peek(4) == 0x1e5;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x11c7);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s341(s11, gas - 1)
      else
        ExecuteFromCFGNode_s340(s11, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 260
    * Starting at 0x11c1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x463

    requires s0.stack[6] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x463;
      assert s1.Peek(7) == 0x1e5;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s341(s5, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 261
    * Starting at 0x11c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x463

    requires s0.stack[6] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x463;
      assert s1.Peek(6) == 0x1e5;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x11e7);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s343(s8, gas - 1)
      else
        ExecuteFromCFGNode_s342(s8, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 262
    * Starting at 0x11d2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x463

    requires s0.stack[6] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x463;
      assert s1.Peek(7) == 0x1e5;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 343
    * Segment Id for this node is: 263
    * Starting at 0x11e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x463

    requires s0.stack[6] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x463;
      assert s1.Peek(6) == 0x1e5;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s6, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 98
    * Starting at 0x463
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1e5;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup1(s5);
      var s7 := Swap2(s6);
      var s8 := Div(s7);
      var s9 := Mul(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x1e5;
      var s12 := Push1(s11, 0x40);
      var s13 := MLoad(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := MStore(s17);
      var s19 := Dup1(s18);
      var s20 := Swap3(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(5) == 0x1e5;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x048f);
      assert s31.Peek(0) == 0x48f;
      assert s31.Peek(8) == 0x1e5;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x11b3);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s345(s34, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 259
    * Starting at 0x11b3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x48f

    requires s0.stack[8] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x48f;
      assert s1.Peek(8) == 0x1e5;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x11c7);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s347(s11, gas - 1)
      else
        ExecuteFromCFGNode_s346(s11, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 260
    * Starting at 0x11c1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x48f

    requires s0.stack[10] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x48f;
      assert s1.Peek(11) == 0x1e5;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s347(s5, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 261
    * Starting at 0x11c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x48f

    requires s0.stack[10] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x48f;
      assert s1.Peek(10) == 0x1e5;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x11e7);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s349(s8, gas - 1)
      else
        ExecuteFromCFGNode_s348(s8, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 262
    * Starting at 0x11d2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x48f

    requires s0.stack[10] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x48f;
      assert s1.Peek(11) == 0x1e5;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 349
    * Segment Id for this node is: 263
    * Starting at 0x11e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x48f

    requires s0.stack[10] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x48f;
      assert s1.Peek(10) == 0x1e5;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s6, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 99
    * Starting at 0x48f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1e5;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x04dc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s353(s5, gas - 1)
      else
        ExecuteFromCFGNode_s351(s5, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 100
    * Starting at 0x496
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x496 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0x1e5;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x04b1);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s359(s5, gas - 1)
      else
        ExecuteFromCFGNode_s352(s5, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 101
    * Starting at 0x49e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0x1e5;
      var s2 := Dup1(s1);
      var s3 := Dup4(s2);
      var s4 := SLoad(s3);
      var s5 := Div(s4);
      var s6 := Mul(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x1e5;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x04dc);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s14, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 105
    * Starting at 0x4dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1e5;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Swap1(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s354(s10, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 50
    * Starting at 0x1e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01f2);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x106a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s8, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 232
    * Starting at 0x106a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1f2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1f2;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x1f2;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s356(s14, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 233
    * Starting at 0x107b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1f2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1f2;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x1097);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s358(s7, gas - 1)
      else
        ExecuteFromCFGNode_s357(s7, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 234
    * Starting at 0x1084
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1084 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1f2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x1f2;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Add(s10);
      assert s11.Peek(8) == 0x1f2;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x107b);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s16, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 235
    * Starting at 0x1097
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1097 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1f2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1f2;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(7) == 0x1f2;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap3(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x1f2;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s28, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 102
    * Starting at 0x4b1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1e5;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Push1(s8, 0x00);
      var s10 := Keccak256(s9);
      var s11 := Swap1(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s360(s11, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 103
    * Starting at 0x4bf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1e5;
      var s2 := Dup2(s1);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x1e5;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x04bf);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s360(s16, gas - 1)
      else
        ExecuteFromCFGNode_s361(s16, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 104
    * Starting at 0x4d3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0x1e5;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s353(s8, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 74
    * Starting at 0x317
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x317 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s363(s9, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 75
    * Starting at 0x324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x324 as nat
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
      var s16 := Push2(s15, 0x01f2);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s17, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 73
    * Starting at 0x30e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0222);
      var s3 := Push1(s2, 0x09);
      var s4 := SLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s6, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 56
    * Starting at 0x222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x222;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x01f2);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s366(s10, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 51
    * Starting at 0x1f2
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x222;
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

  /** Node 367
    * Segment Id for this node is: 25
    * Starting at 0xf9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x50b353f9);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x0166);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s429(s6, gas - 1)
      else
        ExecuteFromCFGNode_s368(s6, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 26
    * Starting at 0x105
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0140);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s406(s5, gas - 1)
      else
        ExecuteFromCFGNode_s369(s5, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 27
    * Starting at 0x110
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x029d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s397(s5, gas - 1)
      else
        ExecuteFromCFGNode_s370(s5, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 28
    * Starting at 0x11b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x715018a6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02c6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s388(s5, gas - 1)
      else
        ExecuteFromCFGNode_s371(s5, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 29
    * Starting at 0x126
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x73d4a13a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02ce);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s385(s5, gas - 1)
      else
        ExecuteFromCFGNode_s372(s5, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 30
    * Starting at 0x131
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x83ae5d9a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02fb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s374(s5, gas - 1)
      else
        ExecuteFromCFGNode_s373(s5, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 31
    * Starting at 0x13c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13c as nat
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

  /** Node 374
    * Segment Id for this node is: 71
    * Starting at 0x2fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01db);
      var s3 := Push2(s2, 0x0309);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1125);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s7, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 245
    * Starting at 0x1125
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1125 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x309

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x309;
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1137);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s377(s10, gas - 1)
      else
        ExecuteFromCFGNode_s376(s10, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 246
    * Starting at 0x1133
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x309

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x309;
      assert s1.Peek(5) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 377
    * Segment Id for this node is: 247
    * Starting at 0x1137
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1137 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x309

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x309;
      assert s1.Peek(4) == 0x1db;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s378(s7, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 72
    * Starting at 0x309
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x309 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x060e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s379(s3, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 123
    * Starting at 0x60e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x0616);
      var s3 := Push2(s2, 0x0a94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s4, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 169
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x616

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x616;
      assert s1.Peek(2) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x616;
      assert s11.Peek(3) == 0x1db;
      var s12 := Push2(s11, 0x060c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s383(s13, gas - 1)
      else
        ExecuteFromCFGNode_s381(s13, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 170
    * Starting at 0xaa7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x616

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x616;
      assert s1.Peek(3) == 0x1db;
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
      assert s11.Peek(3) == 0x616;
      assert s11.Peek(5) == 0x1db;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x616;
      assert s21.Peek(6) == 0x1db;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x058b);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s27, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x616

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x616;
      assert s1.Peek(3) == 0x1db;
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

  /** Node 383
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x616

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x616;
      assert s1.Peek(2) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s384(s2, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 124
    * Starting at 0x616
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x616 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x0a);
      var s3 := SStore(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s4, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 69
    * Starting at 0x2ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x0a);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x0b);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0x0c);
      var s7 := SLoad(s6);
      var s8 := Push2(s7, 0x02e0);
      var s9 := Swap3(s8);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(3) == 0x2e0;
      var s12 := Dup4(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s13, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 70
    * Starting at 0x2e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x2e0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2e0;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap4(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup5(s8);
      var s10 := Add(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(5) == 0x2e0;
      var s12 := Swap1(s11);
      var s13 := Swap3(s12);
      var s14 := MStore(s13);
      var s15 := Swap1(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x01f2);
      assert s21.Peek(0) == 0x1f2;
      assert s21.Peek(2) == 0x2e0;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s387(s22, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 51
    * Starting at 0x1f2
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x2e0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e0;
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

  /** Node 388
    * Segment Id for this node is: 68
    * Starting at 0x2c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01db);
      var s3 := Push2(s2, 0x05fa);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s389(s4, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 120
    * Starting at 0x5fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1db;
      var s2 := Push2(s1, 0x0602);
      var s3 := Push2(s2, 0x0a94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s390(s4, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 169
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x602

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x602;
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x602;
      assert s11.Peek(2) == 0x1db;
      var s12 := Push2(s11, 0x060c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s393(s13, gas - 1)
      else
        ExecuteFromCFGNode_s391(s13, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 170
    * Starting at 0xaa7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x602

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x602;
      assert s1.Peek(2) == 0x1db;
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
      assert s11.Peek(3) == 0x602;
      assert s11.Peek(4) == 0x1db;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x602;
      assert s21.Peek(5) == 0x1db;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x058b);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s392(s27, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x602

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x602;
      assert s1.Peek(2) == 0x1db;
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

  /** Node 393
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x602

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x602;
      assert s1.Peek(1) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s2, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 121
    * Starting at 0x602
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x602 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1db;
      var s2 := Push2(s1, 0x060c);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x0e07);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s395(s5, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 214
    * Starting at 0xe07
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe07 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x60c

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x60c;
      assert s1.Peek(2) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup4(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x60c;
      assert s11.Peek(7) == 0x1db;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Not(s17);
      var s19 := Dup4(s18);
      var s20 := And(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(7) == 0x60c;
      assert s21.Peek(8) == 0x1db;
      var s22 := Or(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Push1(s25, 0x40);
      var s27 := MLoad(s26);
      var s28 := Swap2(s27);
      var s29 := And(s28);
      var s30 := Swap2(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(4) == 0x60c;
      assert s31.Peek(5) == 0x1db;
      var s32 := Dup3(s31);
      var s33 := Swap1(s32);
      var s34 := Push32(s33, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s35 := Swap1(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Swap1(s36);
      var s38 := Log3(s37);
      var s39 := Pop(s38);
      var s40 := Pop(s39);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s41, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s2, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 66
    * Starting at 0x29d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0222);
      var s3 := Push2(s2, 0x02ab);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1046);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s7, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 228
    * Starting at 0x1046
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1046 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2ab

    requires s0.stack[3] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2ab;
      assert s1.Peek(3) == 0x222;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1058);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s400(s10, gas - 1)
      else
        ExecuteFromCFGNode_s399(s10, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 229
    * Starting at 0x1054
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x2ab

    requires s0.stack[4] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2ab;
      assert s1.Peek(5) == 0x222;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 400
    * Segment Id for this node is: 230
    * Starting at 0x1058
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1058 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x2ab

    requires s0.stack[4] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ab;
      assert s1.Peek(4) == 0x222;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x1063);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s401(s7, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x2ab

    requires s0.stack[7] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x2ab;
      assert s1.Peek(7) == 0x222;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x1063;
      assert s11.Peek(8) == 0x2ab;
      assert s11.Peek(9) == 0x222;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s403(s12, gas - 1)
      else
        ExecuteFromCFGNode_s402(s12, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x2ab

    requires s0.stack[7] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(7) == 0x2ab;
      assert s1.Peek(8) == 0x222;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 403
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x2ab

    requires s0.stack[7] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x2ab;
      assert s1.Peek(7) == 0x222;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s3, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 231
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2ab

    requires s0.stack[5] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2ab;
      assert s1.Peek(5) == 0x222;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s7, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 67
    * Starting at 0x2ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x222

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x222;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x222;
      var s12 := Push1(s11, 0x20);
      var s13 := Dup2(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s21, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 32
    * Starting at 0x140
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x50b353f9);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0265);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s420(s6, gas - 1)
      else
        ExecuteFromCFGNode_s407(s6, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 33
    * Starting at 0x14c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x5408d42d);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0288);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s417(s5, gas - 1)
      else
        ExecuteFromCFGNode_s408(s5, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 34
    * Starting at 0x157
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x62256589);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0295);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s410(s5, gas - 1)
      else
        ExecuteFromCFGNode_s409(s5, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 35
    * Starting at 0x162
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x162 as nat
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

  /** Node 410
    * Segment Id for this node is: 65
    * Starting at 0x295
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01db);
      var s3 := Push2(s2, 0x05ea);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s411(s4, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 118
    * Starting at 0x5ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1db;
      var s2 := Push2(s1, 0x05f2);
      var s3 := Push2(s2, 0x0a94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s412(s4, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 169
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x5f2

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5f2;
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x5f2;
      assert s11.Peek(2) == 0x1db;
      var s12 := Push2(s11, 0x060c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s415(s13, gas - 1)
      else
        ExecuteFromCFGNode_s413(s13, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 170
    * Starting at 0xaa7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x5f2

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x5f2;
      assert s1.Peek(2) == 0x1db;
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
      assert s11.Peek(3) == 0x5f2;
      assert s11.Peek(4) == 0x1db;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x5f2;
      assert s21.Peek(5) == 0x1db;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x058b);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s414(s27, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x5f2

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5f2;
      assert s1.Peek(2) == 0x1db;
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

  /** Node 415
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x5f2

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5f2;
      assert s1.Peek(1) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s416(s2, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 119
    * Starting at 0x5f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1db;
      var s2 := Push1(s1, 0x02);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x09);
      var s5 := SStore(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s6, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 64
    * Starting at 0x288
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x288 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x020e);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0xff);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s418(s9, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 54
    * Starting at 0x20e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x20e;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x01f2);
      assert s11.Peek(0) == 0x1f2;
      assert s11.Peek(2) == 0x20e;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s419(s12, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 51
    * Starting at 0x1f2
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x20e;
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

  /** Node 420
    * Segment Id for this node is: 62
    * Starting at 0x265
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x265 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x020e);
      var s3 := Push2(s2, 0x0273);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1046);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s7, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 228
    * Starting at 0x1046
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1046 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x273

    requires s0.stack[3] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x273;
      assert s1.Peek(3) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1058);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s423(s10, gas - 1)
      else
        ExecuteFromCFGNode_s422(s10, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 229
    * Starting at 0x1054
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x273

    requires s0.stack[4] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x273;
      assert s1.Peek(5) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 423
    * Segment Id for this node is: 230
    * Starting at 0x1058
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1058 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x273

    requires s0.stack[4] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x273;
      assert s1.Peek(4) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x1063);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s424(s7, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x273

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x273;
      assert s1.Peek(7) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x1063;
      assert s11.Peek(8) == 0x273;
      assert s11.Peek(9) == 0x20e;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s426(s12, gas - 1)
      else
        ExecuteFromCFGNode_s425(s12, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x273

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(7) == 0x273;
      assert s1.Peek(8) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 426
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x273

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x273;
      assert s1.Peek(7) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s427(s3, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 231
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x273

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x273;
      assert s1.Peek(5) == 0x20e;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s428(s7, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 63
    * Starting at 0x273
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x20e;
      var s2 := Push1(s1, 0x06);
      var s3 := Push1(s2, 0x20);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Swap1(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x20e;
      var s12 := SLoad(s11);
      var s13 := Push1(s12, 0xff);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s418(s16, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 36
    * Starting at 0x166
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x166 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x18160ddd);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x01a2);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s610(s6, gas - 1)
      else
        ExecuteFromCFGNode_s430(s6, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 37
    * Starting at 0x172
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x172 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x021e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s609(s5, gas - 1)
      else
        ExecuteFromCFGNode_s431(s5, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 38
    * Starting at 0x17d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0230);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s458(s5, gas - 1)
      else
        ExecuteFromCFGNode_s432(s5, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 39
    * Starting at 0x188
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x188 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0243);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s457(s5, gas - 1)
      else
        ExecuteFromCFGNode_s433(s5, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 40
    * Starting at 0x193
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x193 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x39509351);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0252);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s435(s5, gas - 1)
      else
        ExecuteFromCFGNode_s434(s5, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 41
    * Starting at 0x19e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19e as nat
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

  /** Node 435
    * Segment Id for this node is: 60
    * Starting at 0x252
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x252 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x020e);
      var s3 := Push2(s2, 0x0260);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x10b8);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s436(s7, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 236
    * Starting at 0x10b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x260

    requires s0.stack[3] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x260;
      assert s1.Peek(3) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x10cb);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s438(s11, gas - 1)
      else
        ExecuteFromCFGNode_s437(s11, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 237
    * Starting at 0x10c7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x260

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x260;
      assert s1.Peek(6) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 438
    * Segment Id for this node is: 238
    * Starting at 0x10cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x260

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x260;
      assert s1.Peek(5) == 0x20e;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x10d6);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s7, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x260

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d6;
      assert s1.Peek(7) == 0x260;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x10d6;
      assert s11.Peek(9) == 0x260;
      assert s11.Peek(10) == 0x20e;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s441(s12, gas - 1)
      else
        ExecuteFromCFGNode_s440(s12, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x260

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x10d6;
      assert s1.Peek(8) == 0x260;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 441
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x260

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d6;
      assert s1.Peek(7) == 0x260;
      assert s1.Peek(8) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s3, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 239
    * Starting at 0x10d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x260

    requires s0.stack[6] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x260;
      assert s1.Peek(6) == 0x20e;
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
      assert s11.Peek(1) == 0x260;
      assert s11.Peek(4) == 0x20e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s13, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 61
    * Starting at 0x260
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x260 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20e;
      var s2 := Push2(s1, 0x05b3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s444(s3, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 116
    * Starting at 0x5b3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20e;
      var s2 := Caller(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x20);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x20e;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup1(s12);
      var s14 := Dup4(s13);
      var s15 := Keccak256(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0xa0);
      var s19 := Shl(s18);
      var s20 := Sub(s19);
      var s21 := Dup8(s20);
      assert s21.Peek(9) == 0x20e;
      var s22 := And(s21);
      var s23 := Dup5(s22);
      var s24 := MStore(s23);
      var s25 := Swap1(s24);
      var s26 := Swap2(s25);
      var s27 := MStore(s26);
      var s28 := Dup2(s27);
      var s29 := Keccak256(s28);
      var s30 := SLoad(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x20e;
      var s32 := Swap2(s31);
      var s33 := Push2(s32, 0x04f3);
      var s34 := Swap2(s33);
      var s35 := Dup6(s34);
      var s36 := Swap1(s35);
      var s37 := Push2(s36, 0x05a3);
      var s38 := Swap1(s37);
      var s39 := Dup7(s38);
      var s40 := Swap1(s39);
      var s41 := Push2(s40, 0x1216);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s445(s41, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 117
    * Starting at 0x5e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x1216

    requires s0.stack[3] == 0x5a3

    requires s0.stack[6] == 0x4f3

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s1, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 267
    * Starting at 0x1216
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x5a3

    requires s0.stack[5] == 0x4f3

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a3;
      assert s1.Peek(5) == 0x4f3;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s449(s10, gas - 1)
      else
        ExecuteFromCFGNode_s447(s10, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 268
    * Starting at 0x1222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x5a3

    requires s0.stack[6] == 0x4f3

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0x5a3;
      assert s1.Peek(7) == 0x4f3;
      assert s1.Peek(11) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s448(s3, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0x5a3

    requires s0.stack[7] == 0x4f3

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0x5a3;
      assert s1.Peek(7) == 0x4f3;
      assert s1.Peek(11) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0x5a3;
      assert s11.Peek(9) == 0x4f3;
      assert s11.Peek(13) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 449
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x5a3

    requires s0.stack[6] == 0x4f3

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a3;
      assert s1.Peek(6) == 0x4f3;
      assert s1.Peek(10) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s6, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 114
    * Starting at 0x5a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f3;
      assert s1.Peek(7) == 0x20e;
      var s2 := Push2(s1, 0x0aee);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s451(s3, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 171
    * Starting at 0xaee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f3;
      assert s1.Peek(7) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0b50);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s453(s10, gas - 1)
      else
        ExecuteFromCFGNode_s452(s10, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 172
    * Starting at 0xafd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
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
      assert s11.Peek(6) == 0x4f3;
      assert s11.Peek(10) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup1(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x4f3;
      assert s21.Peek(10) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push4(s22, 0x72657373);
      var s24 := Push1(s23, 0xe0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x4f3;
      assert s31.Peek(8) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s33, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 173
    * Starting at 0xb50
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f3;
      assert s1.Peek(7) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0bb1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s455(s10, gas - 1)
      else
        ExecuteFromCFGNode_s454(s10, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 174
    * Starting at 0xb5f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x4f3;
      assert s1.Peek(8) == 0x20e;
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
      assert s11.Peek(6) == 0x4f3;
      assert s11.Peek(10) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x22);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x4f3;
      assert s21.Peek(10) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push2(s22, 0x7373);
      var s24 := Push1(s23, 0xf0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x4f3;
      assert s31.Peek(8) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s33, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 175
    * Starting at 0xbb1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f3

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f3;
      assert s1.Peek(7) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x4f3;
      assert s11.Peek(11) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x4f3;
      assert s21.Peek(14) == 0x20e;
      var s22 := Keccak256(s21);
      var s23 := Swap5(s22);
      var s24 := Dup8(s23);
      var s25 := And(s24);
      var s26 := Dup1(s25);
      var s27 := Dup5(s26);
      var s28 := MStore(s27);
      var s29 := Swap5(s28);
      var s30 := Dup3(s29);
      var s31 := MStore(s30);
      assert s31.Peek(8) == 0x4f3;
      assert s31.Peek(12) == 0x20e;
      var s32 := Swap2(s31);
      var s33 := Dup3(s32);
      var s34 := Swap1(s33);
      var s35 := Keccak256(s34);
      var s36 := Dup6(s35);
      var s37 := Swap1(s36);
      var s38 := SStore(s37);
      var s39 := Swap1(s38);
      var s40 := MLoad(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s456(s41, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 176
    * Starting at 0xbe1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x4f3

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x4f3;
      assert s1.Peek(13) == 0x20e;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Swap2(s8);
      var s10 := Sub(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x4f3;
      assert s11.Peek(12) == 0x20e;
      var s12 := Log3(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s16, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 59
    * Starting at 0x243
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x12);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x01f2);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s10, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 57
    * Starting at 0x230
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x230 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x020e);
      var s3 := Push2(s2, 0x023e);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x10e4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s7, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 240
    * Starting at 0x10e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x23e

    requires s0.stack[3] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x23e;
      assert s1.Peek(3) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x10f9);
      assert s11.Peek(0) == 0x10f9;
      assert s11.Peek(7) == 0x23e;
      assert s11.Peek(8) == 0x20e;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s461(s12, gas - 1)
      else
        ExecuteFromCFGNode_s460(s12, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 241
    * Starting at 0x10f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x23e

    requires s0.stack[6] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x23e;
      assert s1.Peek(7) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 461
    * Segment Id for this node is: 242
    * Starting at 0x10f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x23e

    requires s0.stack[6] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x23e;
      assert s1.Peek(6) == 0x20e;
      var s2 := Dup4(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x1104);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s7, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1104

    requires s0.stack[8] == 0x23e

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1104;
      assert s1.Peek(8) == 0x23e;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x1104;
      assert s11.Peek(10) == 0x23e;
      assert s11.Peek(11) == 0x20e;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s464(s12, gas - 1)
      else
        ExecuteFromCFGNode_s463(s12, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1104

    requires s0.stack[8] == 0x23e

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1104;
      assert s1.Peek(9) == 0x23e;
      assert s1.Peek(10) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 464
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1104

    requires s0.stack[8] == 0x23e

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1104;
      assert s1.Peek(8) == 0x23e;
      assert s1.Peek(9) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s465(s3, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 243
    * Starting at 0x1104
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1104 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x23e

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x23e;
      assert s1.Peek(7) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x1114);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x1031);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s466(s11, gas - 1)
  }

  /** Node 466
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1114

    requires s0.stack[8] == 0x23e

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1114;
      assert s1.Peek(8) == 0x23e;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x1114;
      assert s11.Peek(10) == 0x23e;
      assert s11.Peek(11) == 0x20e;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s468(s12, gas - 1)
      else
        ExecuteFromCFGNode_s467(s12, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1114

    requires s0.stack[8] == 0x23e

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1114;
      assert s1.Peek(9) == 0x23e;
      assert s1.Peek(10) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 468
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1114

    requires s0.stack[8] == 0x23e

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1114;
      assert s1.Peek(8) == 0x23e;
      assert s1.Peek(9) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s3, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 244
    * Starting at 0x1114
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1114 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x23e

    requires s0.stack[7] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x23e;
      assert s1.Peek(7) == 0x20e;
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
      assert s11.Peek(0) == 0x23e;
      assert s11.Peek(5) == 0x20e;
      var s12 := Swap2(s11);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s470(s16, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 58
    * Starting at 0x23e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20e;
      var s2 := Push2(s1, 0x04fd);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s471(s3, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 109
    * Starting at 0x4fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x050a);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0c12);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s8, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 177
    * Starting at 0xc12
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc12 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x50a

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x50a;
      assert s1.Peek(8) == 0x20e;
      var s2 := Origin(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x06);
      var s8 := Push1(s7, 0x20);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(5) == 0x50a;
      assert s11.Peek(10) == 0x20e;
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0xff);
      var s15 := And(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0c35);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s513(s18, gas - 1)
      else
        ExecuteFromCFGNode_s473(s18, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 178
    * Starting at 0xc2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x50a

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09cb);
      assert s1.Peek(0) == 0x9cb;
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0e59);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s474(s6, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 215
    * Starting at 0xe59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9cb

    requires s0.stack[7] == 0x50a

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9cb;
      assert s1.Peek(7) == 0x50a;
      assert s1.Peek(12) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0ebd);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s477(s10, gas - 1)
      else
        ExecuteFromCFGNode_s475(s10, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 216
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9cb

    requires s0.stack[7] == 0x50a

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x9cb;
      assert s1.Peek(8) == 0x50a;
      assert s1.Peek(13) == 0x20e;
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
      assert s11.Peek(6) == 0x9cb;
      assert s11.Peek(10) == 0x50a;
      assert s11.Peek(15) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x25);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x9cb;
      assert s21.Peek(10) == 0x50a;
      assert s21.Peek(15) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 5, 0x6472657373);
      var s24 := Push1(s23, 0xd8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x9cb;
      assert s31.Peek(8) == 0x50a;
      assert s31.Peek(13) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s33, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x9cb

    requires s0.stack[8] == 0x50a

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9cb;
      assert s1.Peek(8) == 0x50a;
      assert s1.Peek(13) == 0x20e;
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

  /** Node 477
    * Segment Id for this node is: 217
    * Starting at 0xebd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9cb

    requires s0.stack[7] == 0x50a

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9cb;
      assert s1.Peek(7) == 0x50a;
      assert s1.Peek(12) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0f1f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s479(s10, gas - 1)
      else
        ExecuteFromCFGNode_s478(s10, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 218
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9cb

    requires s0.stack[7] == 0x50a

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x9cb;
      assert s1.Peek(8) == 0x50a;
      assert s1.Peek(13) == 0x20e;
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
      assert s11.Peek(6) == 0x9cb;
      assert s11.Peek(10) == 0x50a;
      assert s11.Peek(15) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x23);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x9cb;
      assert s21.Peek(10) == 0x50a;
      assert s21.Peek(15) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push3(s22, 0x657373);
      var s24 := Push1(s23, 0xe8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x9cb;
      assert s31.Peek(8) == 0x50a;
      assert s31.Peek(13) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s33, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 219
    * Starting at 0xf1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9cb

    requires s0.stack[7] == 0x50a

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9cb;
      assert s1.Peek(7) == 0x50a;
      assert s1.Peek(12) == 0x20e;
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
      assert s11.Peek(6) == 0x9cb;
      assert s11.Peek(10) == 0x50a;
      assert s11.Peek(15) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Keccak256(s18);
      var s20 := SLoad(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0x9cb;
      assert s21.Peek(9) == 0x50a;
      assert s21.Peek(14) == 0x20e;
      var s22 := Dup2(s21);
      var s23 := Lt(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x0f97);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s482(s26, gas - 1)
      else
        ExecuteFromCFGNode_s480(s26, gas - 1)
  }

  /** Node 480
    * Segment Id for this node is: 220
    * Starting at 0xf41
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x9cb

    requires s0.stack[8] == 0x50a

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x9cb;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
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
      assert s11.Peek(7) == 0x9cb;
      assert s11.Peek(11) == 0x50a;
      assert s11.Peek(16) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0x9cb;
      assert s21.Peek(11) == 0x50a;
      assert s21.Peek(16) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x616c616e6365);
      var s24 := Push1(s23, 0xd0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0x9cb;
      assert s31.Peek(9) == 0x50a;
      assert s31.Peek(14) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s481(s33, gas - 1)
  }

  /** Node 481
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x9cb

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x9cb;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
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

  /** Node 482
    * Segment Id for this node is: 221
    * Starting at 0xf97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x9cb

    requires s0.stack[8] == 0x50a

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9cb;
      assert s1.Peek(8) == 0x50a;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push2(s1, 0x0fa1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1203);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s483(s6, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 265
    * Starting at 0x1203
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xfa1

    requires s0.stack[7] == 0x9cb

    requires s0.stack[11] == 0x50a

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfa1;
      assert s1.Peek(7) == 0x9cb;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s486(s10, gas - 1)
      else
        ExecuteFromCFGNode_s484(s10, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 266
    * Starting at 0x120f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0x9cb

    requires s0.stack[12] == 0x50a

    requires s0.stack[17] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0x9cb;
      assert s1.Peek(13) == 0x50a;
      assert s1.Peek(18) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s3, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfa1

    requires s0.stack[9] == 0x9cb

    requires s0.stack[13] == 0x50a

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0x9cb;
      assert s1.Peek(13) == 0x50a;
      assert s1.Peek(18) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfa1;
      assert s11.Peek(11) == 0x9cb;
      assert s11.Peek(15) == 0x50a;
      assert s11.Peek(20) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 486
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0x9cb

    requires s0.stack[12] == 0x50a

    requires s0.stack[17] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfa1;
      assert s1.Peek(8) == 0x9cb;
      assert s1.Peek(12) == 0x50a;
      assert s1.Peek(17) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s487(s6, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 222
    * Starting at 0xfa1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x9cb

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x9cb;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup7(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x9cb;
      assert s11.Peek(12) == 0x50a;
      assert s11.Peek(17) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(9) == 0x9cb;
      assert s21.Peek(13) == 0x50a;
      assert s21.Peek(18) == 0x20e;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap1(s25);
      var s27 := Dup6(s26);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x9cb;
      assert s31.Peek(10) == 0x50a;
      assert s31.Peek(15) == 0x20e;
      var s32 := Dup2(s31);
      var s33 := Keccak256(s32);
      var s34 := Dup1(s33);
      var s35 := SLoad(s34);
      var s36 := Dup5(s35);
      var s37 := Swap3(s36);
      var s38 := Swap1(s37);
      var s39 := Push2(s38, 0x0fd7);
      var s40 := Swap1(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s488(s41, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 223
    * Starting at 0xfd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0x9cb

    requires s0.stack[14] == 0x50a

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0x9cb;
      assert s1.Peek(14) == 0x50a;
      assert s1.Peek(19) == 0x20e;
      var s2 := Push2(s1, 0x1216);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s489(s3, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 267
    * Starting at 0x1216
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0x9cb

    requires s0.stack[14] == 0x50a

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0x9cb;
      assert s1.Peek(14) == 0x50a;
      assert s1.Peek(19) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s492(s10, gas - 1)
      else
        ExecuteFromCFGNode_s490(s10, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 268
    * Starting at 0x1222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0x9cb

    requires s0.stack[15] == 0x50a

    requires s0.stack[20] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0x9cb;
      assert s1.Peek(16) == 0x50a;
      assert s1.Peek(21) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s3, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfd7

    requires s0.stack[12] == 0x9cb

    requires s0.stack[16] == 0x50a

    requires s0.stack[21] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0x9cb;
      assert s1.Peek(16) == 0x50a;
      assert s1.Peek(21) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfd7;
      assert s11.Peek(14) == 0x9cb;
      assert s11.Peek(18) == 0x50a;
      assert s11.Peek(23) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 492
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0x9cb

    requires s0.stack[15] == 0x50a

    requires s0.stack[20] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfd7;
      assert s1.Peek(11) == 0x9cb;
      assert s1.Peek(15) == 0x50a;
      assert s1.Peek(20) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s493(s6, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 224
    * Starting at 0xfd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x9cb

    requires s0.stack[12] == 0x50a

    requires s0.stack[17] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x9cb;
      assert s1.Peek(12) == 0x50a;
      assert s1.Peek(17) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0x9cb;
      assert s11.Peek(11) == 0x50a;
      assert s11.Peek(16) == 0x20e;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(7) == 0x9cb;
      assert s21.Peek(11) == 0x50a;
      assert s21.Peek(16) == 0x20e;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x1023);
      var s28 := Swap2(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x1023;
      assert s31.Peek(10) == 0x9cb;
      assert s31.Peek(14) == 0x50a;
      assert s31.Peek(19) == 0x20e;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s494(s34, gas - 1)
  }

  /** Node 494
    * Segment Id for this node is: 225
    * Starting at 0x1023
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1023 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x9cb

    requires s0.stack[12] == 0x50a

    requires s0.stack[17] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x9cb;
      assert s1.Peek(12) == 0x50a;
      assert s1.Peek(17) == 0x20e;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x9cb;
      assert s11.Peek(5) == 0x50a;
      assert s11.Peek(10) == 0x20e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s495(s13, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 160
    * Starting at 0x9cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x50a

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x50a;
      assert s1.Peek(8) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s496(s5, gas - 1)
  }

  /** Node 496
    * Segment Id for this node is: 110
    * Starting at 0x50a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup5(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup4(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(8) == 0x20e;
      var s22 := Caller(s21);
      var s23 := Dup5(s22);
      var s24 := MStore(s23);
      var s25 := Swap1(s24);
      var s26 := Swap2(s25);
      var s27 := MStore(s26);
      var s28 := Swap1(s27);
      var s29 := Keccak256(s28);
      var s30 := SLoad(s29);
      var s31 := Dup3(s30);
      assert s31.Peek(6) == 0x20e;
      var s32 := Dup2(s31);
      var s33 := Lt(s32);
      var s34 := IsZero(s33);
      var s35 := Push2(s34, 0x0594);
      var s36 := JumpI(s35);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s35.stack[1] > 0 then
        ExecuteFromCFGNode_s499(s36, gas - 1)
      else
        ExecuteFromCFGNode_s497(s36, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 111
    * Starting at 0x537
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x537 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x20e;
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
      assert s11.Peek(8) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x28);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732061);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(8) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push8(s22, 0x6c6c6f77616e6365);
      var s24 := Push1(s23, 0xc0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s498(s31, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x20e;
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

  /** Node 499
    * Segment Id for this node is: 113
    * Starting at 0x594
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x594 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x20e;
      var s2 := Push2(s1, 0x05a8);
      var s3 := Dup6(s2);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x05a3);
      var s6 := Dup7(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x1203);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s9, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 265
    * Starting at 0x1203
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x5a3

    requires s0.stack[5] == 0x5a8

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a3;
      assert s1.Peek(5) == 0x5a8;
      assert s1.Peek(11) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s503(s10, gas - 1)
      else
        ExecuteFromCFGNode_s501(s10, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 266
    * Starting at 0x120f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x5a3

    requires s0.stack[6] == 0x5a8

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0x5a3;
      assert s1.Peek(7) == 0x5a8;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s502(s3, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0x5a3

    requires s0.stack[7] == 0x5a8

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0x5a3;
      assert s1.Peek(7) == 0x5a8;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0x5a3;
      assert s11.Peek(9) == 0x5a8;
      assert s11.Peek(15) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 503
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x5a3

    requires s0.stack[6] == 0x5a8

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a3;
      assert s1.Peek(6) == 0x5a8;
      assert s1.Peek(12) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s504(s6, gas - 1)
  }

  /** Node 504
    * Segment Id for this node is: 114
    * Starting at 0x5a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5a8

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a8;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push2(s1, 0x0aee);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s505(s3, gas - 1)
  }

  /** Node 505
    * Segment Id for this node is: 171
    * Starting at 0xaee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5a8

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a8;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0b50);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s508(s10, gas - 1)
      else
        ExecuteFromCFGNode_s506(s10, gas - 1)
  }

  /** Node 506
    * Segment Id for this node is: 172
    * Starting at 0xafd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5a8

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5a8;
      assert s1.Peek(10) == 0x20e;
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
      assert s11.Peek(6) == 0x5a8;
      assert s11.Peek(12) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup1(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x5a8;
      assert s21.Peek(12) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push4(s22, 0x72657373);
      var s24 := Push1(s23, 0xe0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x5a8;
      assert s31.Peek(10) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s507(s33, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x5a8

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5a8;
      assert s1.Peek(10) == 0x20e;
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

  /** Node 508
    * Segment Id for this node is: 173
    * Starting at 0xb50
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5a8

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a8;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0bb1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s510(s10, gas - 1)
      else
        ExecuteFromCFGNode_s509(s10, gas - 1)
  }

  /** Node 509
    * Segment Id for this node is: 174
    * Starting at 0xb5f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5a8

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5a8;
      assert s1.Peek(10) == 0x20e;
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
      assert s11.Peek(6) == 0x5a8;
      assert s11.Peek(12) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x22);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x5a8;
      assert s21.Peek(12) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push2(s22, 0x7373);
      var s24 := Push1(s23, 0xf0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x5a8;
      assert s31.Peek(10) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s507(s33, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 175
    * Starting at 0xbb1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5a8

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a8;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x5a8;
      assert s11.Peek(13) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x5a8;
      assert s21.Peek(16) == 0x20e;
      var s22 := Keccak256(s21);
      var s23 := Swap5(s22);
      var s24 := Dup8(s23);
      var s25 := And(s24);
      var s26 := Dup1(s25);
      var s27 := Dup5(s26);
      var s28 := MStore(s27);
      var s29 := Swap5(s28);
      var s30 := Dup3(s29);
      var s31 := MStore(s30);
      assert s31.Peek(8) == 0x5a8;
      assert s31.Peek(14) == 0x20e;
      var s32 := Swap2(s31);
      var s33 := Dup3(s32);
      var s34 := Swap1(s33);
      var s35 := Keccak256(s34);
      var s36 := Dup6(s35);
      var s37 := Swap1(s36);
      var s38 := SStore(s37);
      var s39 := Swap1(s38);
      var s40 := MLoad(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s511(s41, gas - 1)
  }

  /** Node 511
    * Segment Id for this node is: 176
    * Starting at 0xbe1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x5a8

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x5a8;
      assert s1.Peek(15) == 0x20e;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Swap2(s8);
      var s10 := Sub(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x5a8;
      assert s11.Peek(14) == 0x20e;
      var s12 := Log3(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s512(s16, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 115
    * Starting at 0x5a8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap5(s3);
      var s5 := Swap4(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s10, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 179
    * Starting at 0xc35
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x50a

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x50a;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := Push2(s5, 0x0c87);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s516(s7, gas - 1)
      else
        ExecuteFromCFGNode_s514(s7, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 180
    * Starting at 0xc40
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc40 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x50a

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
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
      assert s11.Peek(6) == 0x50a;
      assert s11.Peek(11) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x547261646520686173206e6f74206265656e206f70656e656420796574000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x50a;
      assert s21.Peek(11) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x058b);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s515(s26, gas - 1)
  }

  /** Node 515
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x50a

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
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

  /** Node 516
    * Segment Id for this node is: 181
    * Starting at 0xc87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x50a

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x50a;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x09);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0c95);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s518(s7, gas - 1)
      else
        ExecuteFromCFGNode_s517(s7, gas - 1)
  }

  /** Node 517
    * Segment Id for this node is: 182
    * Starting at 0xc91
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x50a

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 518
    * Segment Id for this node is: 183
    * Starting at 0xc95
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc95 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x50a

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x50a;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(7) == 0x50a;
      assert s11.Peek(12) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := And(s12);
      var s14 := Push2(s13, 0x0100);
      var s15 := Swap1(s14);
      var s16 := Swap3(s15);
      var s17 := Div(s16);
      var s18 := And(s17);
      var s19 := Eq(s18);
      var s20 := Push2(s19, 0x0cb9);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s608(s21, gas - 1)
      else
        ExecuteFromCFGNode_s519(s21, gas - 1)
  }

  /** Node 519
    * Segment Id for this node is: 184
    * Starting at 0xcb3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x50a

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Push2(s1, 0x0cbc);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s520(s3, gas - 1)
  }

  /** Node 520
    * Segment Id for this node is: 186
    * Starting at 0xcbc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Origin(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x0d);
      var s8 := Push1(s7, 0x20);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(7) == 0x50a;
      assert s11.Peek(12) == 0x20e;
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Swap1(s13);
      var s15 := Swap2(s14);
      var s16 := Pop(s15);
      var s17 := Push1(s16, 0xff);
      var s18 := And(s17);
      var s19 := Dup1(s18);
      var s20 := IsZero(s19);
      var s21 := Push2(s20, 0x0cf0);
      assert s21.Peek(0) == 0xcf0;
      assert s21.Peek(7) == 0x50a;
      assert s21.Peek(12) == 0x20e;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s522(s22, gas - 1)
      else
        ExecuteFromCFGNode_s521(s22, gas - 1)
  }

  /** Node 521
    * Segment Id for this node is: 187
    * Starting at 0xcd9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x50a;
      assert s11.Peek(12) == 0x20e;
      var s12 := Push2(s11, 0x0100);
      var s13 := Swap1(s12);
      var s14 := Swap3(s13);
      var s15 := Div(s14);
      var s16 := And(s15);
      var s17 := Eq(s16);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s522(s17, gas - 1)
  }

  /** Node 522
    * Segment Id for this node is: 188
    * Starting at 0xcf0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0cfc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s524(s5, gas - 1)
      else
        ExecuteFromCFGNode_s523(s5, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 189
    * Starting at 0xcf7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := GasPrice(s2);
      var s4 := Gt(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s524(s4, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 190
    * Starting at 0xcfc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0d15);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s526(s5, gas - 1)
      else
        ExecuteFromCFGNode_s525(s5, gas - 1)
  }

  /** Node 525
    * Segment Id for this node is: 191
    * Starting at 0xd03
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Origin(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Swap1(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(6) == 0x50a;
      assert s11.Peek(11) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := Keccak256(s12);
      var s14 := SLoad(s13);
      var s15 := Gt(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s526(s15, gas - 1)
  }

  /** Node 526
    * Segment Id for this node is: 192
    * Starting at 0xd15
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd15 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0d1f);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s528(s4, gas - 1)
      else
        ExecuteFromCFGNode_s527(s4, gas - 1)
  }

  /** Node 527
    * Segment Id for this node is: 193
    * Starting at 0xd1b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x50a

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 528
    * Segment Id for this node is: 194
    * Starting at 0xd1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x50a

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0d2d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s530(s6, gas - 1)
      else
        ExecuteFromCFGNode_s529(s6, gas - 1)
  }

  /** Node 529
    * Segment Id for this node is: 195
    * Starting at 0xd27
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x0a);
      var s3 := SLoad(s2);
      var s4 := GasPrice(s3);
      var s5 := Gt(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s530(s5, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 196
    * Starting at 0xd2d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0d37);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s532(s4, gas - 1)
      else
        ExecuteFromCFGNode_s531(s4, gas - 1)
  }

  /** Node 531
    * Segment Id for this node is: 197
    * Starting at 0xd33
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x50a

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 532
    * Segment Id for this node is: 198
    * Starting at 0xd37
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x50a

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup6(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x50a;
      assert s11.Peek(12) == 0x20e;
      var s12 := Push2(s11, 0x0100);
      var s13 := Swap1(s12);
      var s14 := Swap3(s13);
      var s15 := Div(s14);
      var s16 := And(s15);
      var s17 := Eq(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Swap1(s19);
      var s21 := Push2(s20, 0x0d6d);
      assert s21.Peek(0) == 0xd6d;
      assert s21.Peek(7) == 0x50a;
      assert s21.Peek(12) == 0x20e;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s534(s22, gas - 1)
      else
        ExecuteFromCFGNode_s533(s22, gas - 1)
  }

  /** Node 533
    * Segment Id for this node is: 199
    * Starting at 0xd55
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x50a;
      assert s11.Peek(12) == 0x20e;
      var s12 := Push2(s11, 0x0100);
      var s13 := Swap1(s12);
      var s14 := Swap3(s13);
      var s15 := Div(s14);
      var s16 := And(s15);
      var s17 := Eq(s16);
      var s18 := IsZero(s17);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s534(s18, gas - 1)
  }

  /** Node 534
    * Segment Id for this node is: 200
    * Starting at 0xd6d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0d98);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s537(s4, gas - 1)
      else
        ExecuteFromCFGNode_s535(s4, gas - 1)
  }

  /** Node 535
    * Segment Id for this node is: 201
    * Starting at 0xd73
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x50a

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup5(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x50a;
      assert s11.Peek(10) == 0x20e;
      var s12 := Push1(s11, 0x0d);
      var s13 := Push1(s12, 0x20);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Swap1(s15);
      var s17 := Keccak256(s16);
      var s18 := SLoad(s17);
      var s19 := Push1(s18, 0xff);
      var s20 := And(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(5) == 0x50a;
      assert s21.Peek(10) == 0x20e;
      var s22 := Push2(s21, 0x0d98);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s537(s23, gas - 1)
      else
        ExecuteFromCFGNode_s536(s23, gas - 1)
  }

  /** Node 536
    * Segment Id for this node is: 202
    * Starting at 0xd94
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x50a

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 537
    * Segment Id for this node is: 203
    * Starting at 0xd98
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x50a

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0dbf);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s599(s6, gas - 1)
      else
        ExecuteFromCFGNode_s538(s6, gas - 1)
  }

  /** Node 538
    * Segment Id for this node is: 204
    * Starting at 0xda1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x0c);
      assert s1.Peek(6) == 0x50a;
      assert s1.Peek(11) == 0x20e;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x64);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0db0);
      var s6 := Swap1(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x127c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s539(s9, gas - 1)
  }

  /** Node 539
    * Segment Id for this node is: 278
    * Starting at 0x127c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xdb0

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb0;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0xdb0;
      assert s11.Peek(12) == 0x50a;
      assert s11.Peek(17) == 0x20e;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x04f7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s542(s14, gas - 1)
      else
        ExecuteFromCFGNode_s540(s14, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 279
    * Starting at 0x128c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xdb0

    requires s0.stack[10] == 0x50a

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdb0;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s541(s3, gas - 1)
  }

  /** Node 541
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xdb0

    requires s0.stack[11] == 0x50a

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdb0;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xdb0;
      assert s11.Peek(13) == 0x50a;
      assert s11.Peek(18) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 542
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xdb0

    requires s0.stack[10] == 0x50a

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb0;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s543(s6, gas - 1)
  }

  /** Node 543
    * Segment Id for this node is: 205
    * Starting at 0xdb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x50a

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x50a;
      assert s1.Peek(12) == 0x20e;
      var s2 := Push2(s1, 0x0dba);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x1293);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s544(s6, gas - 1)
  }

  /** Node 544
    * Segment Id for this node is: 280
    * Starting at 0x1293
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1293 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xdba

    requires s0.stack[8] == 0x50a

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdba;
      assert s1.Peek(8) == 0x50a;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x12b0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s546(s5, gas - 1)
      else
        ExecuteFromCFGNode_s545(s5, gas - 1)
  }

  /** Node 545
    * Segment Id for this node is: 281
    * Starting at 0x129b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdba

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0xdba;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x12);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 546
    * Segment Id for this node is: 282
    * Starting at 0x12b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdba

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdba;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s547(s5, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 206
    * Starting at 0xdba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x50a

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x50a;
      assert s1.Peek(11) == 0x20e;
      var s2 := Push2(s1, 0x0dd9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s548(s3, gas - 1)
  }

  /** Node 548
    * Segment Id for this node is: 209
    * Starting at 0xdd9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x50a

    requires s0.stack[11] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x50a;
      assert s1.Peek(11) == 0x20e;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0def);
      var s5 := Dup6(s4);
      var s6 := Dup6(s5);
      var s7 := Push2(s6, 0x0dea);
      var s8 := Dup5(s7);
      var s9 := Dup8(s8);
      var s10 := Push2(s9, 0x1203);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s549(s11, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 265
    * Starting at 0x1203
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xdea

    requires s0.stack[5] == 0xdef

    requires s0.stack[11] == 0x50a

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdea;
      assert s1.Peek(5) == 0xdef;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s552(s10, gas - 1)
      else
        ExecuteFromCFGNode_s550(s10, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 266
    * Starting at 0x120f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xdea

    requires s0.stack[6] == 0xdef

    requires s0.stack[12] == 0x50a

    requires s0.stack[17] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdea;
      assert s1.Peek(7) == 0xdef;
      assert s1.Peek(13) == 0x50a;
      assert s1.Peek(18) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s551(s3, gas - 1)
  }

  /** Node 551
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xdea

    requires s0.stack[7] == 0xdef

    requires s0.stack[13] == 0x50a

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdea;
      assert s1.Peek(7) == 0xdef;
      assert s1.Peek(13) == 0x50a;
      assert s1.Peek(18) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xdea;
      assert s11.Peek(9) == 0xdef;
      assert s11.Peek(15) == 0x50a;
      assert s11.Peek(20) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 552
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xdea

    requires s0.stack[6] == 0xdef

    requires s0.stack[12] == 0x50a

    requires s0.stack[17] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdea;
      assert s1.Peek(6) == 0xdef;
      assert s1.Peek(12) == 0x50a;
      assert s1.Peek(17) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s553(s6, gas - 1)
  }

  /** Node 553
    * Segment Id for this node is: 210
    * Starting at 0xdea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdef;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
      var s2 := Push2(s1, 0x0e59);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s554(s3, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 215
    * Starting at 0xe59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdef;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0ebd);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s557(s10, gas - 1)
      else
        ExecuteFromCFGNode_s555(s10, gas - 1)
  }

  /** Node 555
    * Segment Id for this node is: 216
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xdef;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
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
      assert s11.Peek(6) == 0xdef;
      assert s11.Peek(12) == 0x50a;
      assert s11.Peek(17) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x25);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xdef;
      assert s21.Peek(12) == 0x50a;
      assert s21.Peek(17) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 5, 0x6472657373);
      var s24 := Push1(s23, 0xd8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0xdef;
      assert s31.Peek(10) == 0x50a;
      assert s31.Peek(15) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s556(s33, gas - 1)
  }

  /** Node 556
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xdef

    requires s0.stack[10] == 0x50a

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xdef;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
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

  /** Node 557
    * Segment Id for this node is: 217
    * Starting at 0xebd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s557(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdef;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0f1f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s559(s10, gas - 1)
      else
        ExecuteFromCFGNode_s558(s10, gas - 1)
  }

  /** Node 558
    * Segment Id for this node is: 218
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s558(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xdef;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
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
      assert s11.Peek(6) == 0xdef;
      assert s11.Peek(12) == 0x50a;
      assert s11.Peek(17) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x23);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xdef;
      assert s21.Peek(12) == 0x50a;
      assert s21.Peek(17) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push3(s22, 0x657373);
      var s24 := Push1(s23, 0xe8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0xdef;
      assert s31.Peek(10) == 0x50a;
      assert s31.Peek(15) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s556(s33, gas - 1)
  }

  /** Node 559
    * Segment Id for this node is: 219
    * Starting at 0xf1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s559(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdef

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdef;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
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
      assert s11.Peek(6) == 0xdef;
      assert s11.Peek(12) == 0x50a;
      assert s11.Peek(17) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Keccak256(s18);
      var s20 := SLoad(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0xdef;
      assert s21.Peek(11) == 0x50a;
      assert s21.Peek(16) == 0x20e;
      var s22 := Dup2(s21);
      var s23 := Lt(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x0f97);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s562(s26, gas - 1)
      else
        ExecuteFromCFGNode_s560(s26, gas - 1)
  }

  /** Node 560
    * Segment Id for this node is: 220
    * Starting at 0xf41
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s560(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xdef

    requires s0.stack[10] == 0x50a

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0xdef;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
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
      assert s11.Peek(7) == 0xdef;
      assert s11.Peek(13) == 0x50a;
      assert s11.Peek(18) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0xdef;
      assert s21.Peek(13) == 0x50a;
      assert s21.Peek(18) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x616c616e6365);
      var s24 := Push1(s23, 0xd0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0xdef;
      assert s31.Peek(11) == 0x50a;
      assert s31.Peek(16) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s561(s33, gas - 1)
  }

  /** Node 561
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s561(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xdef

    requires s0.stack[11] == 0x50a

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xdef;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
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

  /** Node 562
    * Segment Id for this node is: 221
    * Starting at 0xf97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s562(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xdef

    requires s0.stack[10] == 0x50a

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xdef;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
      var s2 := Push2(s1, 0x0fa1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1203);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s563(s6, gas - 1)
  }

  /** Node 563
    * Segment Id for this node is: 265
    * Starting at 0x1203
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s563(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xfa1

    requires s0.stack[7] == 0xdef

    requires s0.stack[13] == 0x50a

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfa1;
      assert s1.Peek(7) == 0xdef;
      assert s1.Peek(13) == 0x50a;
      assert s1.Peek(18) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s566(s10, gas - 1)
      else
        ExecuteFromCFGNode_s564(s10, gas - 1)
  }

  /** Node 564
    * Segment Id for this node is: 266
    * Starting at 0x120f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s564(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0xdef

    requires s0.stack[14] == 0x50a

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0xdef;
      assert s1.Peek(15) == 0x50a;
      assert s1.Peek(20) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s565(s3, gas - 1)
  }

  /** Node 565
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s565(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfa1

    requires s0.stack[9] == 0xdef

    requires s0.stack[15] == 0x50a

    requires s0.stack[20] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0xdef;
      assert s1.Peek(15) == 0x50a;
      assert s1.Peek(20) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfa1;
      assert s11.Peek(11) == 0xdef;
      assert s11.Peek(17) == 0x50a;
      assert s11.Peek(22) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 566
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s566(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0xdef

    requires s0.stack[14] == 0x50a

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfa1;
      assert s1.Peek(8) == 0xdef;
      assert s1.Peek(14) == 0x50a;
      assert s1.Peek(19) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s567(s6, gas - 1)
  }

  /** Node 567
    * Segment Id for this node is: 222
    * Starting at 0xfa1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s567(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xdef

    requires s0.stack[11] == 0x50a

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xdef;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup7(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0xdef;
      assert s11.Peek(14) == 0x50a;
      assert s11.Peek(19) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(9) == 0xdef;
      assert s21.Peek(15) == 0x50a;
      assert s21.Peek(20) == 0x20e;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap1(s25);
      var s27 := Dup6(s26);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0xdef;
      assert s31.Peek(12) == 0x50a;
      assert s31.Peek(17) == 0x20e;
      var s32 := Dup2(s31);
      var s33 := Keccak256(s32);
      var s34 := Dup1(s33);
      var s35 := SLoad(s34);
      var s36 := Dup5(s35);
      var s37 := Swap3(s36);
      var s38 := Swap1(s37);
      var s39 := Push2(s38, 0x0fd7);
      var s40 := Swap1(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s568(s41, gas - 1)
  }

  /** Node 568
    * Segment Id for this node is: 223
    * Starting at 0xfd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s568(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0xdef

    requires s0.stack[16] == 0x50a

    requires s0.stack[21] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0xdef;
      assert s1.Peek(16) == 0x50a;
      assert s1.Peek(21) == 0x20e;
      var s2 := Push2(s1, 0x1216);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s569(s3, gas - 1)
  }

  /** Node 569
    * Segment Id for this node is: 267
    * Starting at 0x1216
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s569(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0xdef

    requires s0.stack[16] == 0x50a

    requires s0.stack[21] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0xdef;
      assert s1.Peek(16) == 0x50a;
      assert s1.Peek(21) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s572(s10, gas - 1)
      else
        ExecuteFromCFGNode_s570(s10, gas - 1)
  }

  /** Node 570
    * Segment Id for this node is: 268
    * Starting at 0x1222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s570(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0xdef

    requires s0.stack[17] == 0x50a

    requires s0.stack[22] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0xdef;
      assert s1.Peek(18) == 0x50a;
      assert s1.Peek(23) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s571(s3, gas - 1)
  }

  /** Node 571
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s571(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfd7

    requires s0.stack[12] == 0xdef

    requires s0.stack[18] == 0x50a

    requires s0.stack[23] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0xdef;
      assert s1.Peek(18) == 0x50a;
      assert s1.Peek(23) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfd7;
      assert s11.Peek(14) == 0xdef;
      assert s11.Peek(20) == 0x50a;
      assert s11.Peek(25) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 572
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s572(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0xdef

    requires s0.stack[17] == 0x50a

    requires s0.stack[22] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfd7;
      assert s1.Peek(11) == 0xdef;
      assert s1.Peek(17) == 0x50a;
      assert s1.Peek(22) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s573(s6, gas - 1)
  }

  /** Node 573
    * Segment Id for this node is: 224
    * Starting at 0xfd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s573(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0xdef

    requires s0.stack[14] == 0x50a

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xdef;
      assert s1.Peek(14) == 0x50a;
      assert s1.Peek(19) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0xdef;
      assert s11.Peek(13) == 0x50a;
      assert s11.Peek(18) == 0x20e;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(7) == 0xdef;
      assert s21.Peek(13) == 0x50a;
      assert s21.Peek(18) == 0x20e;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x1023);
      var s28 := Swap2(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x1023;
      assert s31.Peek(10) == 0xdef;
      assert s31.Peek(16) == 0x50a;
      assert s31.Peek(21) == 0x20e;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s574(s34, gas - 1)
  }

  /** Node 574
    * Segment Id for this node is: 225
    * Starting at 0x1023
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s574(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1023 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0xdef

    requires s0.stack[14] == 0x50a

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xdef;
      assert s1.Peek(14) == 0x50a;
      assert s1.Peek(19) == 0x20e;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0xdef;
      assert s11.Peek(7) == 0x50a;
      assert s11.Peek(12) == 0x20e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s575(s13, gas - 1)
  }

  /** Node 575
    * Segment Id for this node is: 211
    * Starting at 0xdef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s575(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0e00);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s598(s5, gas - 1)
      else
        ExecuteFromCFGNode_s576(s5, gas - 1)
  }

  /** Node 576
    * Segment Id for this node is: 212
    * Starting at 0xdf6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s576(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e00);
      assert s1.Peek(0) == 0xe00;
      assert s1.Peek(6) == 0x50a;
      assert s1.Peek(11) == 0x20e;
      var s2 := Dup6(s1);
      var s3 := Address(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0e59);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s577(s6, gas - 1)
  }

  /** Node 577
    * Segment Id for this node is: 215
    * Starting at 0xe59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s577(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xe00

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe00;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0ebd);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s580(s10, gas - 1)
      else
        ExecuteFromCFGNode_s578(s10, gas - 1)
  }

  /** Node 578
    * Segment Id for this node is: 216
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s578(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xe00

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xe00;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
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
      assert s11.Peek(6) == 0xe00;
      assert s11.Peek(12) == 0x50a;
      assert s11.Peek(17) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x25);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xe00;
      assert s21.Peek(12) == 0x50a;
      assert s21.Peek(17) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 5, 0x6472657373);
      var s24 := Push1(s23, 0xd8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0xe00;
      assert s31.Peek(10) == 0x50a;
      assert s31.Peek(15) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s579(s33, gas - 1)
  }

  /** Node 579
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s579(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xe00

    requires s0.stack[10] == 0x50a

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe00;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
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

  /** Node 580
    * Segment Id for this node is: 217
    * Starting at 0xebd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s580(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xe00

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe00;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0f1f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s582(s10, gas - 1)
      else
        ExecuteFromCFGNode_s581(s10, gas - 1)
  }

  /** Node 581
    * Segment Id for this node is: 218
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s581(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xe00

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xe00;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
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
      assert s11.Peek(6) == 0xe00;
      assert s11.Peek(12) == 0x50a;
      assert s11.Peek(17) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x23);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xe00;
      assert s21.Peek(12) == 0x50a;
      assert s21.Peek(17) == 0x20e;
      var s22 := MStore(s21);
      var s23 := Push3(s22, 0x657373);
      var s24 := Push1(s23, 0xe8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0xe00;
      assert s31.Peek(10) == 0x50a;
      assert s31.Peek(15) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s579(s33, gas - 1)
  }

  /** Node 582
    * Segment Id for this node is: 219
    * Starting at 0xf1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s582(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xe00

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe00;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
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
      assert s11.Peek(6) == 0xe00;
      assert s11.Peek(12) == 0x50a;
      assert s11.Peek(17) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Keccak256(s18);
      var s20 := SLoad(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0xe00;
      assert s21.Peek(11) == 0x50a;
      assert s21.Peek(16) == 0x20e;
      var s22 := Dup2(s21);
      var s23 := Lt(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x0f97);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s585(s26, gas - 1)
      else
        ExecuteFromCFGNode_s583(s26, gas - 1)
  }

  /** Node 583
    * Segment Id for this node is: 220
    * Starting at 0xf41
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s583(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xe00

    requires s0.stack[10] == 0x50a

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0xe00;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
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
      assert s11.Peek(7) == 0xe00;
      assert s11.Peek(13) == 0x50a;
      assert s11.Peek(18) == 0x20e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0xe00;
      assert s21.Peek(13) == 0x50a;
      assert s21.Peek(18) == 0x20e;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x616c616e6365);
      var s24 := Push1(s23, 0xd0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0xe00;
      assert s31.Peek(11) == 0x50a;
      assert s31.Peek(16) == 0x20e;
      var s32 := Push2(s31, 0x058b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s584(s33, gas - 1)
  }

  /** Node 584
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s584(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe00

    requires s0.stack[11] == 0x50a

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe00;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
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

  /** Node 585
    * Segment Id for this node is: 221
    * Starting at 0xf97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s585(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xe00

    requires s0.stack[10] == 0x50a

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe00;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
      var s2 := Push2(s1, 0x0fa1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1203);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s586(s6, gas - 1)
  }

  /** Node 586
    * Segment Id for this node is: 265
    * Starting at 0x1203
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s586(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xfa1

    requires s0.stack[7] == 0xe00

    requires s0.stack[13] == 0x50a

    requires s0.stack[18] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfa1;
      assert s1.Peek(7) == 0xe00;
      assert s1.Peek(13) == 0x50a;
      assert s1.Peek(18) == 0x20e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s589(s10, gas - 1)
      else
        ExecuteFromCFGNode_s587(s10, gas - 1)
  }

  /** Node 587
    * Segment Id for this node is: 266
    * Starting at 0x120f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s587(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0xe00

    requires s0.stack[14] == 0x50a

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0xe00;
      assert s1.Peek(15) == 0x50a;
      assert s1.Peek(20) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s588(s3, gas - 1)
  }

  /** Node 588
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s588(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfa1

    requires s0.stack[9] == 0xe00

    requires s0.stack[15] == 0x50a

    requires s0.stack[20] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(9) == 0xe00;
      assert s1.Peek(15) == 0x50a;
      assert s1.Peek(20) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfa1;
      assert s11.Peek(11) == 0xe00;
      assert s11.Peek(17) == 0x50a;
      assert s11.Peek(22) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 589
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s589(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xfa1

    requires s0.stack[8] == 0xe00

    requires s0.stack[14] == 0x50a

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfa1;
      assert s1.Peek(8) == 0xe00;
      assert s1.Peek(14) == 0x50a;
      assert s1.Peek(19) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s590(s6, gas - 1)
  }

  /** Node 590
    * Segment Id for this node is: 222
    * Starting at 0xfa1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s590(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe00

    requires s0.stack[11] == 0x50a

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe00;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup7(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0xe00;
      assert s11.Peek(14) == 0x50a;
      assert s11.Peek(19) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(9) == 0xe00;
      assert s21.Peek(15) == 0x50a;
      assert s21.Peek(20) == 0x20e;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap1(s25);
      var s27 := Dup6(s26);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0xe00;
      assert s31.Peek(12) == 0x50a;
      assert s31.Peek(17) == 0x20e;
      var s32 := Dup2(s31);
      var s33 := Keccak256(s32);
      var s34 := Dup1(s33);
      var s35 := SLoad(s34);
      var s36 := Dup5(s35);
      var s37 := Swap3(s36);
      var s38 := Swap1(s37);
      var s39 := Push2(s38, 0x0fd7);
      var s40 := Swap1(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s591(s41, gas - 1)
  }

  /** Node 591
    * Segment Id for this node is: 223
    * Starting at 0xfd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s591(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0xe00

    requires s0.stack[16] == 0x50a

    requires s0.stack[21] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0xe00;
      assert s1.Peek(16) == 0x50a;
      assert s1.Peek(21) == 0x20e;
      var s2 := Push2(s1, 0x1216);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s592(s3, gas - 1)
  }

  /** Node 592
    * Segment Id for this node is: 267
    * Starting at 0x1216
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s592(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xfd7

    requires s0.stack[10] == 0xe00

    requires s0.stack[16] == 0x50a

    requires s0.stack[21] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfd7;
      assert s1.Peek(10) == 0xe00;
      assert s1.Peek(16) == 0x50a;
      assert s1.Peek(21) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04f7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s595(s10, gas - 1)
      else
        ExecuteFromCFGNode_s593(s10, gas - 1)
  }

  /** Node 593
    * Segment Id for this node is: 268
    * Starting at 0x1222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s593(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0xe00

    requires s0.stack[17] == 0x50a

    requires s0.stack[22] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0xe00;
      assert s1.Peek(18) == 0x50a;
      assert s1.Peek(23) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s594(s3, gas - 1)
  }

  /** Node 594
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s594(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xfd7

    requires s0.stack[12] == 0xe00

    requires s0.stack[18] == 0x50a

    requires s0.stack[23] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xfd7;
      assert s1.Peek(12) == 0xe00;
      assert s1.Peek(18) == 0x50a;
      assert s1.Peek(23) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xfd7;
      assert s11.Peek(14) == 0xe00;
      assert s11.Peek(20) == 0x50a;
      assert s11.Peek(25) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 595
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s595(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0xfd7

    requires s0.stack[11] == 0xe00

    requires s0.stack[17] == 0x50a

    requires s0.stack[22] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfd7;
      assert s1.Peek(11) == 0xe00;
      assert s1.Peek(17) == 0x50a;
      assert s1.Peek(22) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s596(s6, gas - 1)
  }

  /** Node 596
    * Segment Id for this node is: 224
    * Starting at 0xfd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s596(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0xe00

    requires s0.stack[14] == 0x50a

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xe00;
      assert s1.Peek(14) == 0x50a;
      assert s1.Peek(19) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0xe00;
      assert s11.Peek(13) == 0x50a;
      assert s11.Peek(18) == 0x20e;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(7) == 0xe00;
      assert s21.Peek(13) == 0x50a;
      assert s21.Peek(18) == 0x20e;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x1023);
      var s28 := Swap2(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x1023;
      assert s31.Peek(10) == 0xe00;
      assert s31.Peek(16) == 0x50a;
      assert s31.Peek(21) == 0x20e;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s597(s34, gas - 1)
  }

  /** Node 597
    * Segment Id for this node is: 225
    * Starting at 0x1023
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s597(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1023 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0xe00

    requires s0.stack[14] == 0x50a

    requires s0.stack[19] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xe00;
      assert s1.Peek(14) == 0x50a;
      assert s1.Peek(19) == 0x20e;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0xe00;
      assert s11.Peek(7) == 0x50a;
      assert s11.Peek(12) == 0x20e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s598(s13, gas - 1)
  }

  /** Node 598
    * Segment Id for this node is: 213
    * Starting at 0xe00
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s598(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s496(s7, gas - 1)
  }

  /** Node 599
    * Segment Id for this node is: 207
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s599(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x50a

    requires s0.stack[10] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50a;
      assert s1.Peek(10) == 0x20e;
      var s2 := Push1(s1, 0x0b);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x64);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0dcf);
      var s7 := Swap1(s6);
      var s8 := Dup6(s7);
      var s9 := Push2(s8, 0x127c);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s600(s10, gas - 1)
  }

  /** Node 600
    * Segment Id for this node is: 278
    * Starting at 0x127c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s600(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xdcf

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdcf;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0xdcf;
      assert s11.Peek(12) == 0x50a;
      assert s11.Peek(17) == 0x20e;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x04f7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s603(s14, gas - 1)
      else
        ExecuteFromCFGNode_s601(s14, gas - 1)
  }

  /** Node 601
    * Segment Id for this node is: 279
    * Starting at 0x128c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s601(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xdcf

    requires s0.stack[10] == 0x50a

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f7);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdcf;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
      var s2 := Push2(s1, 0x11ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s602(s3, gas - 1)
  }

  /** Node 602
    * Segment Id for this node is: 264
    * Starting at 0x11ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s602(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x4f7

    requires s0.stack[4] == 0xdcf

    requires s0.stack[11] == 0x50a

    requires s0.stack[16] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f7;
      assert s1.Peek(4) == 0xdcf;
      assert s1.Peek(11) == 0x50a;
      assert s1.Peek(16) == 0x20e;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f7;
      assert s11.Peek(6) == 0xdcf;
      assert s11.Peek(13) == 0x50a;
      assert s11.Peek(18) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 603
    * Segment Id for this node is: 108
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s603(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xdcf

    requires s0.stack[10] == 0x50a

    requires s0.stack[15] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdcf;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s604(s6, gas - 1)
  }

  /** Node 604
    * Segment Id for this node is: 208
    * Starting at 0xdcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s604(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x50a

    requires s0.stack[12] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x50a;
      assert s1.Peek(12) == 0x20e;
      var s2 := Push2(s1, 0x0dd9);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x1293);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s605(s6, gas - 1)
  }

  /** Node 605
    * Segment Id for this node is: 280
    * Starting at 0x1293
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s605(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1293 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xdd9

    requires s0.stack[8] == 0x50a

    requires s0.stack[13] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdd9;
      assert s1.Peek(8) == 0x50a;
      assert s1.Peek(13) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x12b0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s607(s5, gas - 1)
      else
        ExecuteFromCFGNode_s606(s5, gas - 1)
  }

  /** Node 606
    * Segment Id for this node is: 281
    * Starting at 0x129b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s606(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdd9

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0xdd9;
      assert s1.Peek(10) == 0x50a;
      assert s1.Peek(15) == 0x20e;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x12);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 607
    * Segment Id for this node is: 282
    * Starting at 0x12b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s607(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xdd9

    requires s0.stack[9] == 0x50a

    requires s0.stack[14] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdd9;
      assert s1.Peek(9) == 0x50a;
      assert s1.Peek(14) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s548(s5, gas - 1)
  }

  /** Node 608
    * Segment Id for this node is: 185
    * Starting at 0xcb9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s608(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x50a

    requires s0.stack[9] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x50a;
      assert s1.Peek(9) == 0x20e;
      var s2 := Push1(s1, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s520(s2, gas - 1)
  }

  /** Node 609
    * Segment Id for this node is: 55
    * Starting at 0x21e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s609(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x02);
      var s3 := SLoad(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s106(s3, gas - 1)
  }

  /** Node 610
    * Segment Id for this node is: 42
    * Starting at 0x1a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s610(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push3(s2, 0xf80de2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x01c8);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s626(s6, gas - 1)
      else
        ExecuteFromCFGNode_s611(s6, gas - 1)
  }

  /** Node 611
    * Segment Id for this node is: 43
    * Starting at 0x1ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s611(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x06fdde03);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01dd);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s624(s5, gas - 1)
      else
        ExecuteFromCFGNode_s612(s5, gas - 1)
  }

  /** Node 612
    * Segment Id for this node is: 44
    * Starting at 0x1b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s612(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01fb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s614(s5, gas - 1)
      else
        ExecuteFromCFGNode_s613(s5, gas - 1)
  }

  /** Node 613
    * Segment Id for this node is: 45
    * Starting at 0x1c3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s613(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 614
    * Segment Id for this node is: 52
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s614(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x020e);
      var s3 := Push2(s2, 0x0209);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x10b8);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s615(s7, gas - 1)
  }

  /** Node 615
    * Segment Id for this node is: 236
    * Starting at 0x10b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s615(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x209

    requires s0.stack[3] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x209;
      assert s1.Peek(3) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x10cb);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s617(s11, gas - 1)
      else
        ExecuteFromCFGNode_s616(s11, gas - 1)
  }

  /** Node 616
    * Segment Id for this node is: 237
    * Starting at 0x10c7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s616(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x209

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x209;
      assert s1.Peek(6) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 617
    * Segment Id for this node is: 238
    * Starting at 0x10cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s617(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x209

    requires s0.stack[5] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x209;
      assert s1.Peek(5) == 0x20e;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x10d6);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s618(s7, gas - 1)
  }

  /** Node 618
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s618(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x209

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d6;
      assert s1.Peek(7) == 0x209;
      assert s1.Peek(8) == 0x20e;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x10d6;
      assert s11.Peek(9) == 0x209;
      assert s11.Peek(10) == 0x20e;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s620(s12, gas - 1)
      else
        ExecuteFromCFGNode_s619(s12, gas - 1)
  }

  /** Node 619
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s619(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x209

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x10d6;
      assert s1.Peek(8) == 0x209;
      assert s1.Peek(9) == 0x20e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 620
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s620(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10d6

    requires s0.stack[7] == 0x209

    requires s0.stack[8] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10d6;
      assert s1.Peek(7) == 0x209;
      assert s1.Peek(8) == 0x20e;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s621(s3, gas - 1)
  }

  /** Node 621
    * Segment Id for this node is: 239
    * Starting at 0x10d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s621(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x209

    requires s0.stack[6] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x209;
      assert s1.Peek(6) == 0x20e;
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
      assert s11.Peek(1) == 0x209;
      assert s11.Peek(4) == 0x20e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s622(s13, gas - 1)
  }

  /** Node 622
    * Segment Id for this node is: 53
    * Starting at 0x209
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s622(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x209 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20e;
      var s2 := Push2(s1, 0x04e6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s623(s3, gas - 1)
  }

  /** Node 623
    * Segment Id for this node is: 106
    * Starting at 0x4e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s623(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20e;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x04f3);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0aee);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s451(s8, gas - 1)
  }

  /** Node 624
    * Segment Id for this node is: 49
    * Starting at 0x1dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s624(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e5);
      var s3 := Push2(s2, 0x0454);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s625(s4, gas - 1)
  }

  /** Node 625
    * Segment Id for this node is: 97
    * Starting at 0x454
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s625(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x454 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e5;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x03);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x0463);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x11b3);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s9, gas - 1)
  }

  /** Node 626
    * Segment Id for this node is: 46
    * Starting at 0x1c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s626(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01db);
      var s3 := Push2(s2, 0x01d6);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1046);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s627(s7, gas - 1)
  }

  /** Node 627
    * Segment Id for this node is: 228
    * Starting at 0x1046
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s627(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1046 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1d6

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1d6;
      assert s1.Peek(3) == 0x1db;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1058);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s629(s10, gas - 1)
      else
        ExecuteFromCFGNode_s628(s10, gas - 1)
  }

  /** Node 628
    * Segment Id for this node is: 229
    * Starting at 0x1054
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s628(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1d6

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1d6;
      assert s1.Peek(5) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 629
    * Segment Id for this node is: 230
    * Starting at 0x1058
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s629(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1058 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1d6

    requires s0.stack[4] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1d6;
      assert s1.Peek(4) == 0x1db;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x1063);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s630(s7, gas - 1)
  }

  /** Node 630
    * Segment Id for this node is: 226
    * Starting at 0x1031
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s630(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x1d6

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x1d6;
      assert s1.Peek(7) == 0x1db;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(3) == 0x1063;
      assert s11.Peek(8) == 0x1d6;
      assert s11.Peek(9) == 0x1db;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s632(s12, gas - 1)
      else
        ExecuteFromCFGNode_s631(s12, gas - 1)
  }

  /** Node 631
    * Segment Id for this node is: 227
    * Starting at 0x1042
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s631(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1042 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x1d6

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1063;
      assert s1.Peek(7) == 0x1d6;
      assert s1.Peek(8) == 0x1db;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 632
    * Segment Id for this node is: 150
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s632(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1063

    requires s0.stack[6] == 0x1d6

    requires s0.stack[7] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1063;
      assert s1.Peek(6) == 0x1d6;
      assert s1.Peek(7) == 0x1db;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s633(s3, gas - 1)
  }

  /** Node 633
    * Segment Id for this node is: 231
    * Starting at 0x1063
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s633(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1063 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1d6

    requires s0.stack[5] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1d6;
      assert s1.Peek(5) == 0x1db;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s634(s7, gas - 1)
  }

  /** Node 634
    * Segment Id for this node is: 47
    * Starting at 0x1d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s634(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x042a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s635(s3, gas - 1)
  }

  /** Node 635
    * Segment Id for this node is: 95
    * Starting at 0x42a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s635(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push2(s1, 0x0432);
      var s3 := Push2(s2, 0x0a94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s636(s4, gas - 1)
  }

  /** Node 636
    * Segment Id for this node is: 169
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s636(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x432

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x432;
      assert s1.Peek(2) == 0x1db;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x432;
      assert s11.Peek(3) == 0x1db;
      var s12 := Push2(s11, 0x060c);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s639(s13, gas - 1)
      else
        ExecuteFromCFGNode_s637(s13, gas - 1)
  }

  /** Node 637
    * Segment Id for this node is: 170
    * Starting at 0xaa7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s637(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x432

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x432;
      assert s1.Peek(3) == 0x1db;
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
      assert s11.Peek(3) == 0x432;
      assert s11.Peek(5) == 0x1db;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x432;
      assert s21.Peek(6) == 0x1db;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x058b);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s638(s27, gas - 1)
  }

  /** Node 638
    * Segment Id for this node is: 112
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s638(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x432

    requires s0.stack[3] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x432;
      assert s1.Peek(3) == 0x1db;
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

  /** Node 639
    * Segment Id for this node is: 122
    * Starting at 0x60c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s639(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x432

    requires s0.stack[2] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x432;
      assert s1.Peek(2) == 0x1db;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s640(s2, gas - 1)
  }

  /** Node 640
    * Segment Id for this node is: 96
    * Starting at 0x432
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s640(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x432 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1db

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1db;
      var s2 := Push1(s1, 0x08);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Not(s9);
      var s11 := And(s10);
      assert s11.Peek(3) == 0x1db;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Swap3(s16);
      var s18 := Swap1(s17);
      var s19 := Swap3(s18);
      var s20 := And(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(3) == 0x1db;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := Or(s23);
      var s25 := Swap1(s24);
      var s26 := SStore(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s27, gas - 1)
  }

  /** Node 641
    * Segment Id for this node is: 45
    * Starting at 0x1c3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s641(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
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
