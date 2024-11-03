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
      var s6 := Push2(s5, 0x00ea);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s639(s7, gas - 1)
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
      var s6 := Push4(s5, 0x715018a6);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x008c);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s301(s9, gas - 1)
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
      var s2 := Push4(s1, 0xa457c2d7);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0066);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s226(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa457c2d7);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x024f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s157(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x027f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s5, gas - 1)
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
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02af);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s5, gas - 1)
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
      var s4 := Push2(s3, 0x02df);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
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
      var s1 := Push2(s0, 0x00ea);
      assert s1.Peek(0) == 0xea;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 23
    * Starting at 0xea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
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

  /** Node 11
    * Segment Id for this node is: 69
    * Starting at 0x2df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x02f9);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x02f4);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x2f4;
      assert s11.Peek(3) == 0x2f9;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d35);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s14, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 173
    * Starting at 0xd35
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2f4

    requires s0.stack[3] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2f4;
      assert s1.Peek(3) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d47);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s10, gas - 1)
      else
        ExecuteFromCFGNode_s13(s10, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 174
    * Starting at 0xd43
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x2f4

    requires s0.stack[4] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2f4;
      assert s1.Peek(5) == 0x2f9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 14
    * Segment Id for this node is: 175
    * Starting at 0xd47
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd47 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x2f4

    requires s0.stack[4] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f4;
      assert s1.Peek(4) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d55);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d0b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s9, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 169
    * Starting at 0xd0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xd55

    requires s0.stack[7] == 0x2f4

    requires s0.stack[8] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd55;
      assert s1.Peek(7) == 0x2f4;
      assert s1.Peek(8) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d1a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x152d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s10, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 281
    * Starting at 0x152d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd55

    requires s0.stack[10] == 0x2f4

    requires s0.stack[11] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xd55;
      assert s1.Peek(10) == 0x2f4;
      assert s1.Peek(11) == 0x2f9;
      var s2 := Push2(s1, 0x1536);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s5, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1536

    requires s0.stack[3] == 0xd1a

    requires s0.stack[7] == 0xd55

    requires s0.stack[12] == 0x2f4

    requires s0.stack[13] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1536;
      assert s1.Peek(3) == 0xd1a;
      assert s1.Peek(7) == 0xd55;
      assert s1.Peek(12) == 0x2f4;
      assert s1.Peek(13) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s6, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0x1536

    requires s0.stack[6] == 0xd1a

    requires s0.stack[10] == 0xd55

    requires s0.stack[15] == 0x2f4

    requires s0.stack[16] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0x1536;
      assert s1.Peek(6) == 0xd1a;
      assert s1.Peek(10) == 0xd55;
      assert s1.Peek(15) == 0x2f4;
      assert s1.Peek(16) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s11, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1536

    requires s0.stack[5] == 0xd1a

    requires s0.stack[9] == 0xd55

    requires s0.stack[14] == 0x2f4

    requires s0.stack[15] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1536;
      assert s1.Peek(5) == 0xd1a;
      assert s1.Peek(9) == 0xd55;
      assert s1.Peek(14) == 0x2f4;
      assert s1.Peek(15) == 0x2f9;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s7, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 282
    * Starting at 0x1536
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xd1a

    requires s0.stack[6] == 0xd55

    requires s0.stack[11] == 0x2f4

    requires s0.stack[12] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xd55;
      assert s1.Peek(11) == 0x2f4;
      assert s1.Peek(12) == 0x2f9;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1541);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s5, gas - 1)
      else
        ExecuteFromCFGNode_s21(s5, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 283
    * Starting at 0x153d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd55

    requires s0.stack[10] == 0x2f4

    requires s0.stack[11] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xd55;
      assert s1.Peek(11) == 0x2f4;
      assert s1.Peek(12) == 0x2f9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 22
    * Segment Id for this node is: 284
    * Starting at 0x1541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd55

    requires s0.stack[10] == 0x2f4

    requires s0.stack[11] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xd55;
      assert s1.Peek(10) == 0x2f4;
      assert s1.Peek(11) == 0x2f9;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s3, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 170
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd55

    requires s0.stack[8] == 0x2f4

    requires s0.stack[9] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd55;
      assert s1.Peek(8) == 0x2f4;
      assert s1.Peek(9) == 0x2f9;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s6, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 176
    * Starting at 0xd55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x2f4

    requires s0.stack[6] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2f4;
      assert s1.Peek(6) == 0x2f9;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s9, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 70
    * Starting at 0x2f4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f9;
      var s2 := Push2(s1, 0x0662);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s3, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 121
    * Starting at 0x662
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x662 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f9;
      var s2 := Push2(s1, 0x066a);
      var s3 := Push2(s2, 0x0bbd);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s4, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 159
    * Starting at 0xbbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x66a

    requires s0.stack[2] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x66a;
      assert s1.Peek(2) == 0x2f9;
      var s2 := Push2(s1, 0x0bc5);
      var s3 := Push2(s2, 0x06e6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s4, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 127
    * Starting at 0x6e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0xbc5

    requires s0.stack[1] == 0x66a

    requires s0.stack[3] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xbc5;
      assert s1.Peek(1) == 0x66a;
      assert s1.Peek(3) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s7, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 160
    * Starting at 0xbc5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x66a

    requires s0.stack[3] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x66a;
      assert s1.Peek(3) == 0x2f9;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0be3);
      var s5 := Push2(s4, 0x0485);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s6, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 99
    * Starting at 0x485
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x485 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0xbe3

    requires s0.stack[2] == 0x66a

    requires s0.stack[4] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xbe3;
      assert s1.Peek(2) == 0x66a;
      assert s1.Peek(4) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0xbe3;
      assert s11.Peek(4) == 0x66a;
      assert s11.Peek(6) == 0x2f9;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s17, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 161
    * Starting at 0xbe3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x66a

    requires s0.stack[4] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x66a;
      assert s1.Peek(4) == 0x2f9;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0c39);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s6, gas - 1)
      else
        ExecuteFromCFGNode_s32(s6, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 162
    * Starting at 0xbff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x66a

    requires s0.stack[2] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x66a;
      assert s1.Peek(3) == 0x2f9;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c30);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12dc);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s11, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 240
    * Starting at 0x12dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0xc30

    requires s0.stack[2] == 0x66a

    requires s0.stack[4] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc30;
      assert s1.Peek(2) == 0x66a;
      assert s1.Peek(4) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0xc30;
      assert s11.Peek(5) == 0x66a;
      assert s11.Peek(7) == 0x2f9;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12f5);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1054);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s18, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x12f5

    requires s0.stack[4] == 0xc30

    requires s0.stack[5] == 0x66a

    requires s0.stack[7] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12f5;
      assert s1.Peek(4) == 0xc30;
      assert s1.Peek(5) == 0x66a;
      assert s1.Peek(7) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1061);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s7, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x1061

    requires s0.stack[5] == 0x12f5

    requires s0.stack[8] == 0xc30

    requires s0.stack[9] == 0x66a

    requires s0.stack[11] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1061;
      assert s1.Peek(5) == 0x12f5;
      assert s1.Peek(8) == 0xc30;
      assert s1.Peek(9) == 0x66a;
      assert s1.Peek(11) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1061;
      assert s11.Peek(6) == 0x12f5;
      assert s11.Peek(9) == 0xc30;
      assert s11.Peek(10) == 0x66a;
      assert s11.Peek(12) == 0x2f9;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s15, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 213
    * Starting at 0x1061
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1061 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x12f5

    requires s0.stack[6] == 0xc30

    requires s0.stack[7] == 0x66a

    requires s0.stack[9] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12f5;
      assert s1.Peek(6) == 0xc30;
      assert s1.Peek(7) == 0x66a;
      assert s1.Peek(9) == 0x2f9;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x12f5;
      assert s11.Peek(6) == 0xc30;
      assert s11.Peek(7) == 0x66a;
      assert s11.Peek(9) == 0x2f9;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s17, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 241
    * Starting at 0x12f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0xc30

    requires s0.stack[4] == 0x66a

    requires s0.stack[6] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc30;
      assert s1.Peek(4) == 0x66a;
      assert s1.Peek(6) == 0x2f9;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s7, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 163
    * Starting at 0xc30
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x66a

    requires s0.stack[3] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x66a;
      assert s1.Peek(3) == 0x2f9;
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

  /** Node 39
    * Segment Id for this node is: 164
    * Starting at 0xc39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x66a

    requires s0.stack[2] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x66a;
      assert s1.Peek(2) == 0x2f9;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s2, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 122
    * Starting at 0x66a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x06da);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s11, gas - 1)
      else
        ExecuteFromCFGNode_s41(s11, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 123
    * Starting at 0x6a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x2f9;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x06d1);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x125c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s11, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 232
    * Starting at 0x125c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x6d1

    requires s0.stack[3] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6d1;
      assert s1.Peek(3) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x6d1;
      assert s11.Peek(6) == 0x2f9;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1275);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0ee2);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s18, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 204
    * Starting at 0xee2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x1275

    requires s0.stack[4] == 0x6d1

    requires s0.stack[6] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1275;
      assert s1.Peek(4) == 0x6d1;
      assert s1.Peek(6) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0eef);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s7, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xeef

    requires s0.stack[5] == 0x1275

    requires s0.stack[8] == 0x6d1

    requires s0.stack[10] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeef;
      assert s1.Peek(5) == 0x1275;
      assert s1.Peek(8) == 0x6d1;
      assert s1.Peek(10) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xeef;
      assert s11.Peek(6) == 0x1275;
      assert s11.Peek(9) == 0x6d1;
      assert s11.Peek(11) == 0x2f9;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s15, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 205
    * Starting at 0xeef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x1275

    requires s0.stack[6] == 0x6d1

    requires s0.stack[8] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1275;
      assert s1.Peek(6) == 0x6d1;
      assert s1.Peek(8) == 0x2f9;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x4f776e61626c653a206e6577206f776e657220697320746865207a65726f2061);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x6464726573730000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1275;
      assert s11.Peek(8) == 0x6d1;
      assert s11.Peek(10) == 0x2f9;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1275;
      assert s21.Peek(4) == 0x6d1;
      assert s21.Peek(6) == 0x2f9;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s22, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 233
    * Starting at 0x1275
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1275 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x6d1

    requires s0.stack[5] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6d1;
      assert s1.Peek(5) == 0x2f9;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s7, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 124
    * Starting at 0x6d1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2f9;
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

  /** Node 48
    * Segment Id for this node is: 125
    * Starting at 0x6da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f9;
      var s2 := Push2(s1, 0x06e3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c3b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s5, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 165
    * Starting at 0xc3b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x6e3

    requires s0.stack[3] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6e3;
      assert s1.Peek(3) == 0x2f9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x6e3;
      assert s11.Peek(5) == 0x2f9;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x05);
      var s18 := Push1(s17, 0x00);
      var s19 := Push2(s18, 0x0100);
      var s20 := Exp(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x6e3;
      assert s21.Peek(8) == 0x2f9;
      var s22 := SLoad(s21);
      var s23 := Dup2(s22);
      var s24 := Push20(s23, 0xffffffffffffffffffffffffffffffffffffffff);
      var s25 := Mul(s24);
      var s26 := Not(s25);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Dup4(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(7) == 0x6e3;
      assert s31.Peek(9) == 0x2f9;
      var s32 := Mul(s31);
      var s33 := Or(s32);
      var s34 := Swap1(s33);
      var s35 := SStore(s34);
      var s36 := Pop(s35);
      var s37 := Dup2(s36);
      var s38 := Push20(s37, 0xffffffffffffffffffffffffffffffffffffffff);
      var s39 := And(s38);
      var s40 := Dup2(s39);
      var s41 := Push20(s40, 0xffffffffffffffffffffffffffffffffffffffff);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s50(s41, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 166
    * Starting at 0xcd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x6e3

    requires s0.stack[7] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(4) == 0x6e3;
      assert s1.Peek(6) == 0x2f9;
      var s2 := Push32(s1, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Swap2(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Log3(s10);
      assert s11.Peek(2) == 0x6e3;
      assert s11.Peek(4) == 0x2f9;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s14, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 126
    * Starting at 0x6e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x2f9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f9;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s3, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 71
    * Starting at 0x2f9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
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

  /** Node 53
    * Segment Id for this node is: 65
    * Starting at 0x2af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x02c9);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x02c4);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x2c4;
      assert s11.Peek(3) == 0x2c9;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d5e);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s14, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 177
    * Starting at 0xd5e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2c4

    requires s0.stack[3] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2c4;
      assert s1.Peek(3) == 0x2c9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0d71);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s11, gas - 1)
      else
        ExecuteFromCFGNode_s55(s11, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 178
    * Starting at 0xd6d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2c4

    requires s0.stack[5] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x2c4;
      assert s1.Peek(6) == 0x2c9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 56
    * Segment Id for this node is: 179
    * Starting at 0xd71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2c4

    requires s0.stack[5] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2c4;
      assert s1.Peek(5) == 0x2c9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d7f);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d0b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s9, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 169
    * Starting at 0xd0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xd7f

    requires s0.stack[8] == 0x2c4

    requires s0.stack[9] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd7f;
      assert s1.Peek(8) == 0x2c4;
      assert s1.Peek(9) == 0x2c9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d1a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x152d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s10, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 281
    * Starting at 0x152d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd7f

    requires s0.stack[11] == 0x2c4

    requires s0.stack[12] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xd7f;
      assert s1.Peek(11) == 0x2c4;
      assert s1.Peek(12) == 0x2c9;
      var s2 := Push2(s1, 0x1536);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s5, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1536

    requires s0.stack[3] == 0xd1a

    requires s0.stack[7] == 0xd7f

    requires s0.stack[13] == 0x2c4

    requires s0.stack[14] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1536;
      assert s1.Peek(3) == 0xd1a;
      assert s1.Peek(7) == 0xd7f;
      assert s1.Peek(13) == 0x2c4;
      assert s1.Peek(14) == 0x2c9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s6, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0x1536

    requires s0.stack[6] == 0xd1a

    requires s0.stack[10] == 0xd7f

    requires s0.stack[16] == 0x2c4

    requires s0.stack[17] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0x1536;
      assert s1.Peek(6) == 0xd1a;
      assert s1.Peek(10) == 0xd7f;
      assert s1.Peek(16) == 0x2c4;
      assert s1.Peek(17) == 0x2c9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s11, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1536

    requires s0.stack[5] == 0xd1a

    requires s0.stack[9] == 0xd7f

    requires s0.stack[15] == 0x2c4

    requires s0.stack[16] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1536;
      assert s1.Peek(5) == 0xd1a;
      assert s1.Peek(9) == 0xd7f;
      assert s1.Peek(15) == 0x2c4;
      assert s1.Peek(16) == 0x2c9;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s7, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 282
    * Starting at 0x1536
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd1a

    requires s0.stack[6] == 0xd7f

    requires s0.stack[12] == 0x2c4

    requires s0.stack[13] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xd7f;
      assert s1.Peek(12) == 0x2c4;
      assert s1.Peek(13) == 0x2c9;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1541);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s5, gas - 1)
      else
        ExecuteFromCFGNode_s63(s5, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 283
    * Starting at 0x153d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd7f

    requires s0.stack[11] == 0x2c4

    requires s0.stack[12] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xd7f;
      assert s1.Peek(12) == 0x2c4;
      assert s1.Peek(13) == 0x2c9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 64
    * Segment Id for this node is: 284
    * Starting at 0x1541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd7f

    requires s0.stack[11] == 0x2c4

    requires s0.stack[12] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xd7f;
      assert s1.Peek(11) == 0x2c4;
      assert s1.Peek(12) == 0x2c9;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s3, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 170
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd7f

    requires s0.stack[9] == 0x2c4

    requires s0.stack[10] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd7f;
      assert s1.Peek(9) == 0x2c4;
      assert s1.Peek(10) == 0x2c9;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s6, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 180
    * Starting at 0xd7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x2c4

    requires s0.stack[7] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2c4;
      assert s1.Peek(7) == 0x2c9;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0d90);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d0b);
      assert s11.Peek(0) == 0xd0b;
      assert s11.Peek(3) == 0xd90;
      assert s11.Peek(9) == 0x2c4;
      assert s11.Peek(10) == 0x2c9;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s12, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 169
    * Starting at 0xd0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xd90

    requires s0.stack[8] == 0x2c4

    requires s0.stack[9] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd90;
      assert s1.Peek(8) == 0x2c4;
      assert s1.Peek(9) == 0x2c9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d1a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x152d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s10, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 281
    * Starting at 0x152d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd90

    requires s0.stack[11] == 0x2c4

    requires s0.stack[12] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xd90;
      assert s1.Peek(11) == 0x2c4;
      assert s1.Peek(12) == 0x2c9;
      var s2 := Push2(s1, 0x1536);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s5, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1536

    requires s0.stack[3] == 0xd1a

    requires s0.stack[7] == 0xd90

    requires s0.stack[13] == 0x2c4

    requires s0.stack[14] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1536;
      assert s1.Peek(3) == 0xd1a;
      assert s1.Peek(7) == 0xd90;
      assert s1.Peek(13) == 0x2c4;
      assert s1.Peek(14) == 0x2c9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s6, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0x1536

    requires s0.stack[6] == 0xd1a

    requires s0.stack[10] == 0xd90

    requires s0.stack[16] == 0x2c4

    requires s0.stack[17] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0x1536;
      assert s1.Peek(6) == 0xd1a;
      assert s1.Peek(10) == 0xd90;
      assert s1.Peek(16) == 0x2c4;
      assert s1.Peek(17) == 0x2c9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s11, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1536

    requires s0.stack[5] == 0xd1a

    requires s0.stack[9] == 0xd90

    requires s0.stack[15] == 0x2c4

    requires s0.stack[16] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1536;
      assert s1.Peek(5) == 0xd1a;
      assert s1.Peek(9) == 0xd90;
      assert s1.Peek(15) == 0x2c4;
      assert s1.Peek(16) == 0x2c9;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s7, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 282
    * Starting at 0x1536
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd1a

    requires s0.stack[6] == 0xd90

    requires s0.stack[12] == 0x2c4

    requires s0.stack[13] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xd90;
      assert s1.Peek(12) == 0x2c4;
      assert s1.Peek(13) == 0x2c9;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1541);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s5, gas - 1)
      else
        ExecuteFromCFGNode_s73(s5, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 283
    * Starting at 0x153d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd90

    requires s0.stack[11] == 0x2c4

    requires s0.stack[12] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xd90;
      assert s1.Peek(12) == 0x2c4;
      assert s1.Peek(13) == 0x2c9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 74
    * Segment Id for this node is: 284
    * Starting at 0x1541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd90

    requires s0.stack[11] == 0x2c4

    requires s0.stack[12] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xd90;
      assert s1.Peek(11) == 0x2c4;
      assert s1.Peek(12) == 0x2c9;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s3, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 170
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd90

    requires s0.stack[9] == 0x2c4

    requires s0.stack[10] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd90;
      assert s1.Peek(9) == 0x2c4;
      assert s1.Peek(10) == 0x2c9;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s6, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 181
    * Starting at 0xd90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x2c4

    requires s0.stack[7] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2c4;
      assert s1.Peek(7) == 0x2c9;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s10, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 66
    * Starting at 0x2c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2c9;
      var s2 := Push2(s1, 0x05db);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s3, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 119
    * Starting at 0x5db
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2c9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x2c9;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x2c9;
      var s22 := Dup4(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x2c9;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s79(s41, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 120
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x2c9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x2c9;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s4, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 67
    * Starting at 0x2c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x02d6);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x135c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s8, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 248
    * Starting at 0x135c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2d6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2d6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1371);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1371;
      assert s11.Peek(5) == 0x2d6;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x11c6);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s14, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 220
    * Starting at 0x11c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1371

    requires s0.stack[6] == 0x2d6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1371;
      assert s1.Peek(6) == 0x2d6;
      var s2 := Push2(s1, 0x11cf);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s5, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x11cf

    requires s0.stack[4] == 0x1371

    requires s0.stack[8] == 0x2d6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11cf;
      assert s1.Peek(4) == 0x1371;
      assert s1.Peek(8) == 0x2d6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s9, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 221
    * Starting at 0x11cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1371

    requires s0.stack[7] == 0x2d6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1371;
      assert s1.Peek(7) == 0x2d6;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s6, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 249
    * Starting at 0x1371
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x2d6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2d6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s6, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 68
    * Starting at 0x2d6
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d6 as nat
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

  /** Node 87
    * Segment Id for this node is: 61
    * Starting at 0x27f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0299);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0294);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x294;
      assert s11.Peek(3) == 0x299;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0de9);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s14, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 188
    * Starting at 0xde9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x294

    requires s0.stack[3] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x294;
      assert s1.Peek(3) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0dfc);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s11, gas - 1)
      else
        ExecuteFromCFGNode_s89(s11, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 189
    * Starting at 0xdf8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x294

    requires s0.stack[5] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x294;
      assert s1.Peek(6) == 0x299;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 90
    * Segment Id for this node is: 190
    * Starting at 0xdfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x294

    requires s0.stack[5] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x294;
      assert s1.Peek(5) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0e0a);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d0b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s9, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 169
    * Starting at 0xd0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe0a

    requires s0.stack[8] == 0x294

    requires s0.stack[9] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe0a;
      assert s1.Peek(8) == 0x294;
      assert s1.Peek(9) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d1a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x152d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s10, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 281
    * Starting at 0x152d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x294

    requires s0.stack[12] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xe0a;
      assert s1.Peek(11) == 0x294;
      assert s1.Peek(12) == 0x299;
      var s2 := Push2(s1, 0x1536);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s5, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1536

    requires s0.stack[3] == 0xd1a

    requires s0.stack[7] == 0xe0a

    requires s0.stack[13] == 0x294

    requires s0.stack[14] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1536;
      assert s1.Peek(3) == 0xd1a;
      assert s1.Peek(7) == 0xe0a;
      assert s1.Peek(13) == 0x294;
      assert s1.Peek(14) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s6, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0x1536

    requires s0.stack[6] == 0xd1a

    requires s0.stack[10] == 0xe0a

    requires s0.stack[16] == 0x294

    requires s0.stack[17] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0x1536;
      assert s1.Peek(6) == 0xd1a;
      assert s1.Peek(10) == 0xe0a;
      assert s1.Peek(16) == 0x294;
      assert s1.Peek(17) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s11, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1536

    requires s0.stack[5] == 0xd1a

    requires s0.stack[9] == 0xe0a

    requires s0.stack[15] == 0x294

    requires s0.stack[16] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1536;
      assert s1.Peek(5) == 0xd1a;
      assert s1.Peek(9) == 0xe0a;
      assert s1.Peek(15) == 0x294;
      assert s1.Peek(16) == 0x299;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s7, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 282
    * Starting at 0x1536
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd1a

    requires s0.stack[6] == 0xe0a

    requires s0.stack[12] == 0x294

    requires s0.stack[13] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xe0a;
      assert s1.Peek(12) == 0x294;
      assert s1.Peek(13) == 0x299;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1541);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s5, gas - 1)
      else
        ExecuteFromCFGNode_s97(s5, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 283
    * Starting at 0x153d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x294

    requires s0.stack[12] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xe0a;
      assert s1.Peek(12) == 0x294;
      assert s1.Peek(13) == 0x299;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 98
    * Segment Id for this node is: 284
    * Starting at 0x1541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x294

    requires s0.stack[12] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xe0a;
      assert s1.Peek(11) == 0x294;
      assert s1.Peek(12) == 0x299;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s3, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 170
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe0a

    requires s0.stack[9] == 0x294

    requires s0.stack[10] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe0a;
      assert s1.Peek(9) == 0x294;
      assert s1.Peek(10) == 0x299;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s6, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 191
    * Starting at 0xe0a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x294

    requires s0.stack[7] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x294;
      assert s1.Peek(7) == 0x299;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0e1b);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d20);
      assert s11.Peek(0) == 0xd20;
      assert s11.Peek(3) == 0xe1b;
      assert s11.Peek(9) == 0x294;
      assert s11.Peek(10) == 0x299;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s12, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 171
    * Starting at 0xd20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe1b

    requires s0.stack[8] == 0x294

    requires s0.stack[9] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe1b;
      assert s1.Peek(8) == 0x294;
      assert s1.Peek(9) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d2f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1544);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s10, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 285
    * Starting at 0x1544
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1544 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x294

    requires s0.stack[12] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(5) == 0xe1b;
      assert s1.Peek(11) == 0x294;
      assert s1.Peek(12) == 0x299;
      var s2 := Push2(s1, 0x154d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s5, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x154d

    requires s0.stack[3] == 0xd2f

    requires s0.stack[7] == 0xe1b

    requires s0.stack[13] == 0x294

    requires s0.stack[14] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x154d;
      assert s1.Peek(3) == 0xd2f;
      assert s1.Peek(7) == 0xe1b;
      assert s1.Peek(13) == 0x294;
      assert s1.Peek(14) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s9, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 286
    * Starting at 0x154d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd2f

    requires s0.stack[6] == 0xe1b

    requires s0.stack[12] == 0x294

    requires s0.stack[13] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd2f;
      assert s1.Peek(6) == 0xe1b;
      assert s1.Peek(12) == 0x294;
      assert s1.Peek(13) == 0x299;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1558);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s5, gas - 1)
      else
        ExecuteFromCFGNode_s105(s5, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 287
    * Starting at 0x1554
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1554 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x294

    requires s0.stack[12] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd2f;
      assert s1.Peek(6) == 0xe1b;
      assert s1.Peek(12) == 0x294;
      assert s1.Peek(13) == 0x299;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 106
    * Segment Id for this node is: 288
    * Starting at 0x1558
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1558 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x294

    requires s0.stack[12] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(5) == 0xe1b;
      assert s1.Peek(11) == 0x294;
      assert s1.Peek(12) == 0x299;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s3, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 172
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe1b

    requires s0.stack[9] == 0x294

    requires s0.stack[10] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe1b;
      assert s1.Peek(9) == 0x294;
      assert s1.Peek(10) == 0x299;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s6, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 192
    * Starting at 0xe1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x294

    requires s0.stack[7] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x294;
      assert s1.Peek(7) == 0x299;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s10, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 62
    * Starting at 0x294
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x294 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x299;
      var s2 := Push2(s1, 0x05b8);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s3, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 116
    * Starting at 0x5b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x05c3);
      var s5 := Push2(s4, 0x06e6);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s6, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 127
    * Starting at 0x6e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x5c3

    requires s0.stack[5] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5c3;
      assert s1.Peek(5) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s7, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 117
    * Starting at 0x5c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x299;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x05d0);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x0945);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s9, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 145
    * Starting at 0x945
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x945 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5d0

    requires s0.stack[8] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d0;
      assert s1.Peek(8) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x09b5);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s11, gas - 1)
      else
        ExecuteFromCFGNode_s114(s11, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 146
    * Starting at 0x97b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5d0

    requires s0.stack[8] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5d0;
      assert s1.Peek(9) == 0x299;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x09ac);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12fc);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s11, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 242
    * Starting at 0x12fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x9ac

    requires s0.stack[5] == 0x5d0

    requires s0.stack[10] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9ac;
      assert s1.Peek(5) == 0x5d0;
      assert s1.Peek(10) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x9ac;
      assert s11.Peek(8) == 0x5d0;
      assert s11.Peek(13) == 0x299;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1315);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1094);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s18, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 214
    * Starting at 0x1094
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1315

    requires s0.stack[4] == 0x9ac

    requires s0.stack[8] == 0x5d0

    requires s0.stack[13] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1315;
      assert s1.Peek(4) == 0x9ac;
      assert s1.Peek(8) == 0x5d0;
      assert s1.Peek(13) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x10a1);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s7, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x10a1

    requires s0.stack[5] == 0x1315

    requires s0.stack[8] == 0x9ac

    requires s0.stack[12] == 0x5d0

    requires s0.stack[17] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10a1;
      assert s1.Peek(5) == 0x1315;
      assert s1.Peek(8) == 0x9ac;
      assert s1.Peek(12) == 0x5d0;
      assert s1.Peek(17) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x10a1;
      assert s11.Peek(6) == 0x1315;
      assert s11.Peek(9) == 0x9ac;
      assert s11.Peek(13) == 0x5d0;
      assert s11.Peek(18) == 0x299;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s15, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 215
    * Starting at 0x10a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1315

    requires s0.stack[6] == 0x9ac

    requires s0.stack[10] == 0x5d0

    requires s0.stack[15] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1315;
      assert s1.Peek(6) == 0x9ac;
      assert s1.Peek(10) == 0x5d0;
      assert s1.Peek(15) == 0x299;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x6472657373000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1315;
      assert s11.Peek(8) == 0x9ac;
      assert s11.Peek(12) == 0x5d0;
      assert s11.Peek(17) == 0x299;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1315;
      assert s21.Peek(4) == 0x9ac;
      assert s21.Peek(8) == 0x5d0;
      assert s21.Peek(13) == 0x299;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s22, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 243
    * Starting at 0x1315
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1315 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9ac

    requires s0.stack[7] == 0x5d0

    requires s0.stack[12] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9ac;
      assert s1.Peek(7) == 0x5d0;
      assert s1.Peek(12) == 0x299;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s7, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 147
    * Starting at 0x9ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x5d0

    requires s0.stack[9] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5d0;
      assert s1.Peek(9) == 0x299;
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

  /** Node 121
    * Segment Id for this node is: 148
    * Starting at 0x9b5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5d0

    requires s0.stack[8] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d0;
      assert s1.Peek(8) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0a25);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s129(s11, gas - 1)
      else
        ExecuteFromCFGNode_s122(s11, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 149
    * Starting at 0x9eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5d0

    requires s0.stack[8] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5d0;
      assert s1.Peek(9) == 0x299;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a1c);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x123c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s11, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 230
    * Starting at 0x123c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xa1c

    requires s0.stack[5] == 0x5d0

    requires s0.stack[10] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa1c;
      assert s1.Peek(5) == 0x5d0;
      assert s1.Peek(10) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0xa1c;
      assert s11.Peek(8) == 0x5d0;
      assert s11.Peek(13) == 0x299;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1255);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0e7c);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s18, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 202
    * Starting at 0xe7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1255

    requires s0.stack[4] == 0xa1c

    requires s0.stack[8] == 0x5d0

    requires s0.stack[13] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1255;
      assert s1.Peek(4) == 0xa1c;
      assert s1.Peek(8) == 0x5d0;
      assert s1.Peek(13) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0e89);
      var s4 := Push1(s3, 0x23);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s7, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xe89

    requires s0.stack[5] == 0x1255

    requires s0.stack[8] == 0xa1c

    requires s0.stack[12] == 0x5d0

    requires s0.stack[17] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe89;
      assert s1.Peek(5) == 0x1255;
      assert s1.Peek(8) == 0xa1c;
      assert s1.Peek(12) == 0x5d0;
      assert s1.Peek(17) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xe89;
      assert s11.Peek(6) == 0x1255;
      assert s11.Peek(9) == 0xa1c;
      assert s11.Peek(13) == 0x5d0;
      assert s11.Peek(18) == 0x299;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s15, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 203
    * Starting at 0xe89
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1255

    requires s0.stack[6] == 0xa1c

    requires s0.stack[10] == 0x5d0

    requires s0.stack[15] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1255;
      assert s1.Peek(6) == 0xa1c;
      assert s1.Peek(10) == 0x5d0;
      assert s1.Peek(15) == 0x299;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x6573730000000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1255;
      assert s11.Peek(8) == 0xa1c;
      assert s11.Peek(12) == 0x5d0;
      assert s11.Peek(17) == 0x299;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1255;
      assert s21.Peek(4) == 0xa1c;
      assert s21.Peek(8) == 0x5d0;
      assert s21.Peek(13) == 0x299;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s22, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 231
    * Starting at 0x1255
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1255 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xa1c

    requires s0.stack[7] == 0x5d0

    requires s0.stack[12] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa1c;
      assert s1.Peek(7) == 0x5d0;
      assert s1.Peek(12) == 0x299;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s7, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 150
    * Starting at 0xa1c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x5d0

    requires s0.stack[9] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5d0;
      assert s1.Peek(9) == 0x299;
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

  /** Node 129
    * Segment Id for this node is: 151
    * Starting at 0xa25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5d0

    requires s0.stack[8] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d0;
      assert s1.Peek(8) == 0x299;
      var s2 := Push2(s1, 0x0a30);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d01);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s7, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 167
    * Starting at 0xd01
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd01 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xa30

    requires s0.stack[7] == 0x5d0

    requires s0.stack[12] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa30;
      assert s1.Peek(7) == 0x5d0;
      assert s1.Peek(12) == 0x299;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s5, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 152
    * Starting at 0xa30
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5d0

    requires s0.stack[8] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d0;
      assert s1.Peek(8) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x5d0;
      assert s11.Peek(11) == 0x299;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x5d0;
      assert s21.Peek(10) == 0x299;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0ab6);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s29, gas - 1)
      else
        ExecuteFromCFGNode_s132(s29, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 153
    * Starting at 0xa7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x5d0

    requires s0.stack[9] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x5d0;
      assert s1.Peek(10) == 0x299;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0aad);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12bc);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s11, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 238
    * Starting at 0x12bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xaad

    requires s0.stack[6] == 0x5d0

    requires s0.stack[11] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaad;
      assert s1.Peek(6) == 0x5d0;
      assert s1.Peek(11) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0xaad;
      assert s11.Peek(9) == 0x5d0;
      assert s11.Peek(14) == 0x299;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12d5);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0fee);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s18, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 210
    * Starting at 0xfee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x12d5

    requires s0.stack[4] == 0xaad

    requires s0.stack[9] == 0x5d0

    requires s0.stack[14] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12d5;
      assert s1.Peek(4) == 0xaad;
      assert s1.Peek(9) == 0x5d0;
      assert s1.Peek(14) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ffb);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s7, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xffb

    requires s0.stack[5] == 0x12d5

    requires s0.stack[8] == 0xaad

    requires s0.stack[13] == 0x5d0

    requires s0.stack[18] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xffb;
      assert s1.Peek(5) == 0x12d5;
      assert s1.Peek(8) == 0xaad;
      assert s1.Peek(13) == 0x5d0;
      assert s1.Peek(18) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xffb;
      assert s11.Peek(6) == 0x12d5;
      assert s11.Peek(9) == 0xaad;
      assert s11.Peek(14) == 0x5d0;
      assert s11.Peek(19) == 0x299;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s15, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 211
    * Starting at 0xffb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x12d5

    requires s0.stack[6] == 0xaad

    requires s0.stack[11] == 0x5d0

    requires s0.stack[16] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12d5;
      assert s1.Peek(6) == 0xaad;
      assert s1.Peek(11) == 0x5d0;
      assert s1.Peek(16) == 0x299;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x616c616e63650000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x12d5;
      assert s11.Peek(8) == 0xaad;
      assert s11.Peek(13) == 0x5d0;
      assert s11.Peek(18) == 0x299;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x12d5;
      assert s21.Peek(4) == 0xaad;
      assert s21.Peek(9) == 0x5d0;
      assert s21.Peek(14) == 0x299;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s22, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 239
    * Starting at 0x12d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xaad

    requires s0.stack[8] == 0x5d0

    requires s0.stack[13] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaad;
      assert s1.Peek(8) == 0x5d0;
      assert s1.Peek(13) == 0x299;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s7, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 154
    * Starting at 0xaad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x5d0

    requires s0.stack[10] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x5d0;
      assert s1.Peek(10) == 0x299;
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

  /** Node 139
    * Segment Id for this node is: 155
    * Starting at 0xab6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x5d0

    requires s0.stack[9] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5d0;
      assert s1.Peek(9) == 0x299;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup1(s5);
      var s7 := Dup7(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x5d0;
      assert s11.Peek(13) == 0x299;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(7) == 0x5d0;
      assert s21.Peek(12) == 0x299;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Dup2(s26);
      var s28 := Push1(s27, 0x00);
      var s29 := Dup1(s28);
      var s30 := Dup6(s29);
      var s31 := Push20(s30, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s31.Peek(9) == 0x5d0;
      assert s31.Peek(14) == 0x299;
      var s32 := And(s31);
      var s33 := Push20(s32, 0xffffffffffffffffffffffffffffffffffffffff);
      var s34 := And(s33);
      var s35 := Dup2(s34);
      var s36 := MStore(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Add(s37);
      var s39 := Swap1(s38);
      var s40 := Dup2(s39);
      var s41 := MStore(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s140(s41, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 156
    * Starting at 0xb35
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x5d0

    requires s0.stack[11] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x5d0;
      assert s1.Peek(12) == 0x299;
      var s2 := Add(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Keccak256(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup3(s5);
      var s7 := Dup3(s6);
      var s8 := SLoad(s7);
      var s9 := Add(s8);
      var s10 := Swap3(s9);
      var s11 := Pop(s10);
      assert s11.Peek(7) == 0x5d0;
      assert s11.Peek(12) == 0x299;
      var s12 := Pop(s11);
      var s13 := Dup2(s12);
      var s14 := Swap1(s13);
      var s15 := SStore(s14);
      var s16 := Pop(s15);
      var s17 := Dup3(s16);
      var s18 := Push20(s17, 0xffffffffffffffffffffffffffffffffffffffff);
      var s19 := And(s18);
      var s20 := Dup5(s19);
      var s21 := Push20(s20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s21.Peek(7) == 0x5d0;
      assert s21.Peek(12) == 0x299;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x0ba4);
      var s28 := Swap2(s27);
      var s29 := Swap1(s28);
      var s30 := Push2(s29, 0x135c);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s31, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 248
    * Starting at 0x135c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xba4

    requires s0.stack[10] == 0x5d0

    requires s0.stack[15] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xba4;
      assert s1.Peek(10) == 0x5d0;
      assert s1.Peek(15) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1371);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1371;
      assert s11.Peek(5) == 0xba4;
      assert s11.Peek(13) == 0x5d0;
      assert s11.Peek(18) == 0x299;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x11c6);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s14, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 220
    * Starting at 0x11c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x1371

    requires s0.stack[6] == 0xba4

    requires s0.stack[14] == 0x5d0

    requires s0.stack[19] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1371;
      assert s1.Peek(6) == 0xba4;
      assert s1.Peek(14) == 0x5d0;
      assert s1.Peek(19) == 0x299;
      var s2 := Push2(s1, 0x11cf);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s5, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x11cf

    requires s0.stack[4] == 0x1371

    requires s0.stack[8] == 0xba4

    requires s0.stack[16] == 0x5d0

    requires s0.stack[21] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11cf;
      assert s1.Peek(4) == 0x1371;
      assert s1.Peek(8) == 0xba4;
      assert s1.Peek(16) == 0x5d0;
      assert s1.Peek(21) == 0x299;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s9, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 221
    * Starting at 0x11cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x1371

    requires s0.stack[7] == 0xba4

    requires s0.stack[15] == 0x5d0

    requires s0.stack[20] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1371;
      assert s1.Peek(7) == 0xba4;
      assert s1.Peek(15) == 0x5d0;
      assert s1.Peek(20) == 0x299;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s6, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 249
    * Starting at 0x1371
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xba4

    requires s0.stack[11] == 0x5d0

    requires s0.stack[16] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xba4;
      assert s1.Peek(11) == 0x5d0;
      assert s1.Peek(16) == 0x299;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s6, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 157
    * Starting at 0xba4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x5d0

    requires s0.stack[13] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x5d0;
      assert s1.Peek(13) == 0x299;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push2(s8, 0x0bb7);
      var s10 := Dup5(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(2) == 0xbb7;
      assert s11.Peek(7) == 0x5d0;
      assert s11.Peek(12) == 0x299;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d06);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s14, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 168
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xbb7

    requires s0.stack[8] == 0x5d0

    requires s0.stack[13] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbb7;
      assert s1.Peek(8) == 0x5d0;
      assert s1.Peek(13) == 0x299;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s5, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 158
    * Starting at 0xbb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x5d0

    requires s0.stack[9] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5d0;
      assert s1.Peek(9) == 0x299;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s6, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 118
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x299

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x299;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s10, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 63
    * Starting at 0x299
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x02a6);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11ff);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s8, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 226
    * Starting at 0x11ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x2a6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2a6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1214);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1214;
      assert s11.Peek(5) == 0x2a6;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e34);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s14, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 195
    * Starting at 0xe34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1214

    requires s0.stack[6] == 0x2a6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1214;
      assert s1.Peek(6) == 0x2a6;
      var s2 := Push2(s1, 0x0e3d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1416);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s5, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 262
    * Starting at 0x1416
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1416 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe3d

    requires s0.stack[4] == 0x1214

    requires s0.stack[8] == 0x2a6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe3d;
      assert s1.Peek(4) == 0x1214;
      assert s1.Peek(8) == 0x2a6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s11, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 196
    * Starting at 0xe3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1214

    requires s0.stack[7] == 0x2a6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1214;
      assert s1.Peek(7) == 0x2a6;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s6, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 227
    * Starting at 0x1214
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1214 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x2a6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2a6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s6, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 64
    * Starting at 0x2a6
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a6 as nat
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

  /** Node 157
    * Segment Id for this node is: 57
    * Starting at 0x24f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0269);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0264);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x264;
      assert s11.Peek(3) == 0x269;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0de9);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s14, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 188
    * Starting at 0xde9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x264

    requires s0.stack[3] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x264;
      assert s1.Peek(3) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0dfc);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s160(s11, gas - 1)
      else
        ExecuteFromCFGNode_s159(s11, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 189
    * Starting at 0xdf8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x264

    requires s0.stack[5] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x264;
      assert s1.Peek(6) == 0x269;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 160
    * Segment Id for this node is: 190
    * Starting at 0xdfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x264

    requires s0.stack[5] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x264;
      assert s1.Peek(5) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0e0a);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d0b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s9, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 169
    * Starting at 0xd0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe0a

    requires s0.stack[8] == 0x264

    requires s0.stack[9] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe0a;
      assert s1.Peek(8) == 0x264;
      assert s1.Peek(9) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d1a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x152d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s10, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 281
    * Starting at 0x152d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x264

    requires s0.stack[12] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xe0a;
      assert s1.Peek(11) == 0x264;
      assert s1.Peek(12) == 0x269;
      var s2 := Push2(s1, 0x1536);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s5, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1536

    requires s0.stack[3] == 0xd1a

    requires s0.stack[7] == 0xe0a

    requires s0.stack[13] == 0x264

    requires s0.stack[14] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1536;
      assert s1.Peek(3) == 0xd1a;
      assert s1.Peek(7) == 0xe0a;
      assert s1.Peek(13) == 0x264;
      assert s1.Peek(14) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s6, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0x1536

    requires s0.stack[6] == 0xd1a

    requires s0.stack[10] == 0xe0a

    requires s0.stack[16] == 0x264

    requires s0.stack[17] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0x1536;
      assert s1.Peek(6) == 0xd1a;
      assert s1.Peek(10) == 0xe0a;
      assert s1.Peek(16) == 0x264;
      assert s1.Peek(17) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s11, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1536

    requires s0.stack[5] == 0xd1a

    requires s0.stack[9] == 0xe0a

    requires s0.stack[15] == 0x264

    requires s0.stack[16] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1536;
      assert s1.Peek(5) == 0xd1a;
      assert s1.Peek(9) == 0xe0a;
      assert s1.Peek(15) == 0x264;
      assert s1.Peek(16) == 0x269;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s7, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 282
    * Starting at 0x1536
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd1a

    requires s0.stack[6] == 0xe0a

    requires s0.stack[12] == 0x264

    requires s0.stack[13] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xe0a;
      assert s1.Peek(12) == 0x264;
      assert s1.Peek(13) == 0x269;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1541);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s168(s5, gas - 1)
      else
        ExecuteFromCFGNode_s167(s5, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 283
    * Starting at 0x153d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x264

    requires s0.stack[12] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xe0a;
      assert s1.Peek(12) == 0x264;
      assert s1.Peek(13) == 0x269;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 168
    * Segment Id for this node is: 284
    * Starting at 0x1541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x264

    requires s0.stack[12] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xe0a;
      assert s1.Peek(11) == 0x264;
      assert s1.Peek(12) == 0x269;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s3, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 170
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe0a

    requires s0.stack[9] == 0x264

    requires s0.stack[10] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe0a;
      assert s1.Peek(9) == 0x264;
      assert s1.Peek(10) == 0x269;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s6, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 191
    * Starting at 0xe0a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x264

    requires s0.stack[7] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x264;
      assert s1.Peek(7) == 0x269;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0e1b);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d20);
      assert s11.Peek(0) == 0xd20;
      assert s11.Peek(3) == 0xe1b;
      assert s11.Peek(9) == 0x264;
      assert s11.Peek(10) == 0x269;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s12, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 171
    * Starting at 0xd20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe1b

    requires s0.stack[8] == 0x264

    requires s0.stack[9] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe1b;
      assert s1.Peek(8) == 0x264;
      assert s1.Peek(9) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d2f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1544);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s10, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 285
    * Starting at 0x1544
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1544 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x264

    requires s0.stack[12] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(5) == 0xe1b;
      assert s1.Peek(11) == 0x264;
      assert s1.Peek(12) == 0x269;
      var s2 := Push2(s1, 0x154d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s5, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x154d

    requires s0.stack[3] == 0xd2f

    requires s0.stack[7] == 0xe1b

    requires s0.stack[13] == 0x264

    requires s0.stack[14] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x154d;
      assert s1.Peek(3) == 0xd2f;
      assert s1.Peek(7) == 0xe1b;
      assert s1.Peek(13) == 0x264;
      assert s1.Peek(14) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s9, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 286
    * Starting at 0x154d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd2f

    requires s0.stack[6] == 0xe1b

    requires s0.stack[12] == 0x264

    requires s0.stack[13] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd2f;
      assert s1.Peek(6) == 0xe1b;
      assert s1.Peek(12) == 0x264;
      assert s1.Peek(13) == 0x269;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1558);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s5, gas - 1)
      else
        ExecuteFromCFGNode_s175(s5, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 287
    * Starting at 0x1554
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1554 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x264

    requires s0.stack[12] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd2f;
      assert s1.Peek(6) == 0xe1b;
      assert s1.Peek(12) == 0x264;
      assert s1.Peek(13) == 0x269;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 176
    * Segment Id for this node is: 288
    * Starting at 0x1558
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1558 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x264

    requires s0.stack[12] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(5) == 0xe1b;
      assert s1.Peek(11) == 0x264;
      assert s1.Peek(12) == 0x269;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s3, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 172
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe1b

    requires s0.stack[9] == 0x264

    requires s0.stack[10] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe1b;
      assert s1.Peek(9) == 0x264;
      assert s1.Peek(10) == 0x269;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s6, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 192
    * Starting at 0xe1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x264

    requires s0.stack[7] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x264;
      assert s1.Peek(7) == 0x269;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s10, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 58
    * Starting at 0x264
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x264 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x269;
      var s2 := Push2(s1, 0x0541);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s3, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 109
    * Starting at 0x541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x054c);
      var s5 := Push2(s4, 0x06e6);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s6, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 127
    * Starting at 0x6e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x54c

    requires s0.stack[5] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x54c;
      assert s1.Peek(5) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s7, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 110
    * Starting at 0x54c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x269;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push2(s4, 0x055a);
      var s6 := Dup3(s5);
      var s7 := Dup7(s6);
      var s8 := Push2(s7, 0x05db);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s9, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 119
    * Starting at 0x5db
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x55a

    requires s0.stack[8] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x55a;
      assert s1.Peek(8) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x55a;
      assert s11.Peek(11) == 0x269;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x55a;
      assert s21.Peek(11) == 0x269;
      var s22 := Dup4(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x55a;
      assert s31.Peek(11) == 0x269;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s184(s41, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 120
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x55a

    requires s0.stack[9] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x55a;
      assert s1.Peek(9) == 0x269;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s4, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 111
    * Starting at 0x55a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x269;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup4(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x059f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s9, gas - 1)
      else
        ExecuteFromCFGNode_s186(s9, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 112
    * Starting at 0x565
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x565 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x269;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0596);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x133c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s11, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 246
    * Starting at 0x133c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x133c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x596

    requires s0.stack[7] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x596;
      assert s1.Peek(7) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x596;
      assert s11.Peek(10) == 0x269;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1355);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1160);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s18, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 218
    * Starting at 0x1160
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1160 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x1355

    requires s0.stack[4] == 0x596

    requires s0.stack[10] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1355;
      assert s1.Peek(4) == 0x596;
      assert s1.Peek(10) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x116d);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s7, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x116d

    requires s0.stack[5] == 0x1355

    requires s0.stack[8] == 0x596

    requires s0.stack[14] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x116d;
      assert s1.Peek(5) == 0x1355;
      assert s1.Peek(8) == 0x596;
      assert s1.Peek(14) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x116d;
      assert s11.Peek(6) == 0x1355;
      assert s11.Peek(9) == 0x596;
      assert s11.Peek(15) == 0x269;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s15, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 219
    * Starting at 0x116d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x1355

    requires s0.stack[6] == 0x596

    requires s0.stack[12] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1355;
      assert s1.Peek(6) == 0x596;
      assert s1.Peek(12) == 0x269;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a2064656372656173656420616c6c6f77616e63652062656c6f77);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x207a65726f000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1355;
      assert s11.Peek(8) == 0x596;
      assert s11.Peek(14) == 0x269;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1355;
      assert s21.Peek(4) == 0x596;
      assert s21.Peek(10) == 0x269;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s22, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 247
    * Starting at 0x1355
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1355 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x596

    requires s0.stack[9] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x596;
      assert s1.Peek(9) == 0x269;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s7, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 113
    * Starting at 0x596
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x596 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x269;
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

  /** Node 193
    * Segment Id for this node is: 114
    * Starting at 0x59f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x269;
      var s2 := Push2(s1, 0x05ac);
      var s3 := Dup3(s2);
      var s4 := Dup7(s3);
      var s5 := Dup7(s4);
      var s6 := Dup5(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x06ee);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s9, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 128
    * Starting at 0x6ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5ac

    requires s0.stack[9] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ac;
      assert s1.Peek(9) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x075e);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s11, gas - 1)
      else
        ExecuteFromCFGNode_s195(s11, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 129
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5ac

    requires s0.stack[9] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5ac;
      assert s1.Peek(10) == 0x269;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0755);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x131c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s11, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 244
    * Starting at 0x131c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x755

    requires s0.stack[5] == 0x5ac

    requires s0.stack[11] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x755;
      assert s1.Peek(5) == 0x5ac;
      assert s1.Peek(11) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x755;
      assert s11.Peek(8) == 0x5ac;
      assert s11.Peek(14) == 0x269;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1335);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10fa);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s18, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 216
    * Starting at 0x10fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1335

    requires s0.stack[4] == 0x755

    requires s0.stack[8] == 0x5ac

    requires s0.stack[14] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1335;
      assert s1.Peek(4) == 0x755;
      assert s1.Peek(8) == 0x5ac;
      assert s1.Peek(14) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1107);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s7, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x1107

    requires s0.stack[5] == 0x1335

    requires s0.stack[8] == 0x755

    requires s0.stack[12] == 0x5ac

    requires s0.stack[18] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1107;
      assert s1.Peek(5) == 0x1335;
      assert s1.Peek(8) == 0x755;
      assert s1.Peek(12) == 0x5ac;
      assert s1.Peek(18) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1107;
      assert s11.Peek(6) == 0x1335;
      assert s11.Peek(9) == 0x755;
      assert s11.Peek(13) == 0x5ac;
      assert s11.Peek(19) == 0x269;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s15, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 217
    * Starting at 0x1107
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1107 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1335

    requires s0.stack[6] == 0x755

    requires s0.stack[10] == 0x5ac

    requires s0.stack[16] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1335;
      assert s1.Peek(6) == 0x755;
      assert s1.Peek(10) == 0x5ac;
      assert s1.Peek(16) == 0x269;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1335;
      assert s11.Peek(8) == 0x755;
      assert s11.Peek(12) == 0x5ac;
      assert s11.Peek(18) == 0x269;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1335;
      assert s21.Peek(4) == 0x755;
      assert s21.Peek(8) == 0x5ac;
      assert s21.Peek(14) == 0x269;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s22, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 245
    * Starting at 0x1335
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1335 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x755

    requires s0.stack[7] == 0x5ac

    requires s0.stack[13] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x755;
      assert s1.Peek(7) == 0x5ac;
      assert s1.Peek(13) == 0x269;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s7, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 130
    * Starting at 0x755
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x755 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x5ac

    requires s0.stack[10] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5ac;
      assert s1.Peek(10) == 0x269;
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

  /** Node 202
    * Segment Id for this node is: 131
    * Starting at 0x75e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5ac

    requires s0.stack[9] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ac;
      assert s1.Peek(9) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x07ce);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s210(s11, gas - 1)
      else
        ExecuteFromCFGNode_s203(s11, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 132
    * Starting at 0x794
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x794 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5ac

    requires s0.stack[9] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5ac;
      assert s1.Peek(10) == 0x269;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x07c5);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x127c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s11, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 234
    * Starting at 0x127c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x7c5

    requires s0.stack[5] == 0x5ac

    requires s0.stack[11] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7c5;
      assert s1.Peek(5) == 0x5ac;
      assert s1.Peek(11) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x7c5;
      assert s11.Peek(8) == 0x5ac;
      assert s11.Peek(14) == 0x269;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1295);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0f48);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s18, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 206
    * Starting at 0xf48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1295

    requires s0.stack[4] == 0x7c5

    requires s0.stack[8] == 0x5ac

    requires s0.stack[14] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1295;
      assert s1.Peek(4) == 0x7c5;
      assert s1.Peek(8) == 0x5ac;
      assert s1.Peek(14) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f55);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s7, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xf55

    requires s0.stack[5] == 0x1295

    requires s0.stack[8] == 0x7c5

    requires s0.stack[12] == 0x5ac

    requires s0.stack[18] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf55;
      assert s1.Peek(5) == 0x1295;
      assert s1.Peek(8) == 0x7c5;
      assert s1.Peek(12) == 0x5ac;
      assert s1.Peek(18) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xf55;
      assert s11.Peek(6) == 0x1295;
      assert s11.Peek(9) == 0x7c5;
      assert s11.Peek(13) == 0x5ac;
      assert s11.Peek(19) == 0x269;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s15, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 207
    * Starting at 0xf55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1295

    requires s0.stack[6] == 0x7c5

    requires s0.stack[10] == 0x5ac

    requires s0.stack[16] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1295;
      assert s1.Peek(6) == 0x7c5;
      assert s1.Peek(10) == 0x5ac;
      assert s1.Peek(16) == 0x269;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1295;
      assert s11.Peek(8) == 0x7c5;
      assert s11.Peek(12) == 0x5ac;
      assert s11.Peek(18) == 0x269;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1295;
      assert s21.Peek(4) == 0x7c5;
      assert s21.Peek(8) == 0x5ac;
      assert s21.Peek(14) == 0x269;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s22, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 235
    * Starting at 0x1295
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x7c5

    requires s0.stack[7] == 0x5ac

    requires s0.stack[13] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7c5;
      assert s1.Peek(7) == 0x5ac;
      assert s1.Peek(13) == 0x269;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s7, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 133
    * Starting at 0x7c5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x5ac

    requires s0.stack[10] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5ac;
      assert s1.Peek(10) == 0x269;
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

  /** Node 210
    * Segment Id for this node is: 134
    * Starting at 0x7ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5ac

    requires s0.stack[9] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ac;
      assert s1.Peek(9) == 0x269;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x5ac;
      assert s11.Peek(12) == 0x269;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(6) == 0x5ac;
      assert s21.Peek(12) == 0x269;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x5ac;
      assert s31.Peek(12) == 0x269;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s211(s41, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 135
    * Starting at 0x850
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x850 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x5ac

    requires s0.stack[9] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x5ac;
      assert s1.Peek(10) == 0x269;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08ac);
      assert s11.Peek(0) == 0x8ac;
      assert s11.Peek(9) == 0x5ac;
      assert s11.Peek(15) == 0x269;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x135c);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s15, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 248
    * Starting at 0x135c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x8ac

    requires s0.stack[9] == 0x5ac

    requires s0.stack[15] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8ac;
      assert s1.Peek(9) == 0x5ac;
      assert s1.Peek(15) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1371);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1371;
      assert s11.Peek(5) == 0x8ac;
      assert s11.Peek(12) == 0x5ac;
      assert s11.Peek(18) == 0x269;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x11c6);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s14, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 220
    * Starting at 0x11c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x1371

    requires s0.stack[6] == 0x8ac

    requires s0.stack[13] == 0x5ac

    requires s0.stack[19] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1371;
      assert s1.Peek(6) == 0x8ac;
      assert s1.Peek(13) == 0x5ac;
      assert s1.Peek(19) == 0x269;
      var s2 := Push2(s1, 0x11cf);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s5, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x11cf

    requires s0.stack[4] == 0x1371

    requires s0.stack[8] == 0x8ac

    requires s0.stack[15] == 0x5ac

    requires s0.stack[21] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11cf;
      assert s1.Peek(4) == 0x1371;
      assert s1.Peek(8) == 0x8ac;
      assert s1.Peek(15) == 0x5ac;
      assert s1.Peek(21) == 0x269;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s9, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 221
    * Starting at 0x11cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x1371

    requires s0.stack[7] == 0x8ac

    requires s0.stack[14] == 0x5ac

    requires s0.stack[20] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1371;
      assert s1.Peek(7) == 0x8ac;
      assert s1.Peek(14) == 0x5ac;
      assert s1.Peek(20) == 0x269;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s6, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 249
    * Starting at 0x1371
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x8ac

    requires s0.stack[10] == 0x5ac

    requires s0.stack[16] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8ac;
      assert s1.Peek(10) == 0x5ac;
      assert s1.Peek(16) == 0x269;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s6, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 136
    * Starting at 0x8ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x5ac

    requires s0.stack[13] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x5ac;
      assert s1.Peek(13) == 0x269;
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
      assert s11.Peek(0) == 0x5ac;
      assert s11.Peek(6) == 0x269;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s12, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 115
    * Starting at 0x5ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x269

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x269;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s11, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 59
    * Starting at 0x269
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x269 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0276);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11ff);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s8, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 226
    * Starting at 0x11ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x276

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x276;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1214);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1214;
      assert s11.Peek(5) == 0x276;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e34);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s221(s14, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 195
    * Starting at 0xe34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1214

    requires s0.stack[6] == 0x276

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1214;
      assert s1.Peek(6) == 0x276;
      var s2 := Push2(s1, 0x0e3d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1416);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s5, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 262
    * Starting at 0x1416
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1416 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe3d

    requires s0.stack[4] == 0x1214

    requires s0.stack[8] == 0x276

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe3d;
      assert s1.Peek(4) == 0x1214;
      assert s1.Peek(8) == 0x276;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s11, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 196
    * Starting at 0xe3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1214

    requires s0.stack[7] == 0x276

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1214;
      assert s1.Peek(7) == 0x276;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s6, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 227
    * Starting at 0x1214
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1214 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x276

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x276;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s6, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 60
    * Starting at 0x276
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x276 as nat
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

  /** Node 226
    * Segment Id for this node is: 10
    * Starting at 0x66
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x715018a6);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0209);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s281(s6, gas - 1)
      else
        ExecuteFromCFGNode_s227(s6, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 11
    * Starting at 0x72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0213);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s270(s5, gas - 1)
      else
        ExecuteFromCFGNode_s228(s5, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0231);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s5, gas - 1)
      else
        ExecuteFromCFGNode_s229(s5, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00ea);
      assert s1.Peek(0) == 0xea;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 54
    * Starting at 0x231
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x231 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0239);
      var s3 := Push2(s2, 0x04af);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s4, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 100
    * Starting at 0x4af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x239;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x04be);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x148c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s9, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 272
    * Starting at 0x148c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x148c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x4be

    requires s0.stack[4] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4be;
      assert s1.Peek(4) == 0x239;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x4be;
      assert s11.Peek(7) == 0x239;
      var s12 := Push2(s11, 0x14a4);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s234(s13, gas - 1)
      else
        ExecuteFromCFGNode_s233(s13, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 273
    * Starting at 0x149e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x149e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4be

    requires s0.stack[6] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x4be;
      assert s1.Peek(7) == 0x239;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s234(s5, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 274
    * Starting at 0x14a4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4be

    requires s0.stack[6] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4be;
      assert s1.Peek(6) == 0x239;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x14b8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s237(s9, gas - 1)
      else
        ExecuteFromCFGNode_s235(s9, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 275
    * Starting at 0x14b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4be

    requires s0.stack[6] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x14b7);
      assert s1.Peek(0) == 0x14b7;
      assert s1.Peek(4) == 0x4be;
      assert s1.Peek(7) == 0x239;
      var s2 := Push2(s1, 0x14ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s3, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 279
    * Starting at 0x14ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x14b7

    requires s0.stack[4] == 0x4be

    requires s0.stack[7] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x14b7;
      assert s1.Peek(4) == 0x4be;
      assert s1.Peek(7) == 0x239;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 237
    * Segment Id for this node is: 277
    * Starting at 0x14b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x4be

    requires s0.stack[6] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4be;
      assert s1.Peek(6) == 0x239;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s6, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 101
    * Starting at 0x4be
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x239;
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
      assert s11.Peek(4) == 0x239;
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
      assert s21.Peek(5) == 0x239;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x04ea);
      assert s31.Peek(0) == 0x4ea;
      assert s31.Peek(8) == 0x239;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x148c);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s34, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 272
    * Starting at 0x148c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x148c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x4ea

    requires s0.stack[8] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4ea;
      assert s1.Peek(8) == 0x239;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x4ea;
      assert s11.Peek(11) == 0x239;
      var s12 := Push2(s11, 0x14a4);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s241(s13, gas - 1)
      else
        ExecuteFromCFGNode_s240(s13, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 273
    * Starting at 0x149e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x149e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x4ea

    requires s0.stack[10] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x4ea;
      assert s1.Peek(11) == 0x239;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s241(s5, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 274
    * Starting at 0x14a4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x4ea

    requires s0.stack[10] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4ea;
      assert s1.Peek(10) == 0x239;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x14b8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s244(s9, gas - 1)
      else
        ExecuteFromCFGNode_s242(s9, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 275
    * Starting at 0x14b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x4ea

    requires s0.stack[10] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x14b7);
      assert s1.Peek(0) == 0x14b7;
      assert s1.Peek(4) == 0x4ea;
      assert s1.Peek(11) == 0x239;
      var s2 := Push2(s1, 0x14ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s3, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 279
    * Starting at 0x14ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x14b7

    requires s0.stack[4] == 0x4ea

    requires s0.stack[11] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x14b7;
      assert s1.Peek(4) == 0x4ea;
      assert s1.Peek(11) == 0x239;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 244
    * Segment Id for this node is: 277
    * Starting at 0x14b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x4ea

    requires s0.stack[10] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4ea;
      assert s1.Peek(10) == 0x239;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s6, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 102
    * Starting at 0x4ea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x239;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0537);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s5, gas - 1)
      else
        ExecuteFromCFGNode_s246(s5, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 103
    * Starting at 0x4f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0x239;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x050c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s5, gas - 1)
      else
        ExecuteFromCFGNode_s247(s5, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 104
    * Starting at 0x4f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0x239;
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
      assert s11.Peek(7) == 0x239;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0537);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s14, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 108
    * Starting at 0x537
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x537 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x239;
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
      ExecuteFromCFGNode_s249(s10, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 55
    * Starting at 0x239
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x239 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0246);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x121a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s8, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 228
    * Starting at 0x121a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x246;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x246;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1234);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0e43);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s19, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 197
    * Starting at 0xe43
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1234

    requires s0.stack[6] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1234;
      assert s1.Peek(6) == 0x246;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0e4e);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1392);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s6, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 252
    * Starting at 0x1392
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1392 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xe4e

    requires s0.stack[5] == 0x1234

    requires s0.stack[9] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe4e;
      assert s1.Peek(5) == 0x1234;
      assert s1.Peek(9) == 0x246;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s10, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 198
    * Starting at 0xe4e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x1234

    requires s0.stack[8] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1234;
      assert s1.Peek(8) == 0x246;
      var s2 := Push2(s1, 0x0e58);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x139d);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s6, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xe58

    requires s0.stack[7] == 0x1234

    requires s0.stack[11] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe58;
      assert s1.Peek(7) == 0x1234;
      assert s1.Peek(11) == 0x246;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xe58;
      assert s11.Peek(8) == 0x1234;
      assert s11.Peek(12) == 0x246;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s15, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 199
    * Starting at 0xe58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x1234

    requires s0.stack[9] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1234;
      assert s1.Peek(9) == 0x246;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0e68);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x1459);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s256(s11, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 266
    * Starting at 0x1459
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1459 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xe68

    requires s0.stack[8] == 0x1234

    requires s0.stack[12] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe68;
      assert s1.Peek(8) == 0x1234;
      assert s1.Peek(12) == 0x246;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s257(s2, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 267
    * Starting at 0x145c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x145c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xe68

    requires s0.stack[9] == 0x1234

    requires s0.stack[13] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe68;
      assert s1.Peek(9) == 0x1234;
      assert s1.Peek(13) == 0x246;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x1477);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s259(s7, gas - 1)
      else
        ExecuteFromCFGNode_s258(s7, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 268
    * Starting at 0x1465
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1465 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xe68

    requires s0.stack[9] == 0x1234

    requires s0.stack[13] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xe68;
      assert s1.Peek(10) == 0x1234;
      assert s1.Peek(14) == 0x246;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0xe68;
      assert s11.Peek(10) == 0x1234;
      assert s11.Peek(14) == 0x246;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x145c);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s15, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 269
    * Starting at 0x1477
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1477 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xe68

    requires s0.stack[9] == 0x1234

    requires s0.stack[13] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe68;
      assert s1.Peek(9) == 0x1234;
      assert s1.Peek(13) == 0x246;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x1486);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s261(s7, gas - 1)
      else
        ExecuteFromCFGNode_s260(s7, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 270
    * Starting at 0x1480
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1480 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xe68

    requires s0.stack[9] == 0x1234

    requires s0.stack[13] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xe68;
      assert s1.Peek(10) == 0x1234;
      assert s1.Peek(14) == 0x246;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s261(s5, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 271
    * Starting at 0x1486
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1486 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xe68

    requires s0.stack[9] == 0x1234

    requires s0.stack[13] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe68;
      assert s1.Peek(9) == 0x1234;
      assert s1.Peek(13) == 0x246;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s6, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 200
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x1234

    requires s0.stack[8] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1234;
      assert s1.Peek(8) == 0x246;
      var s2 := Push2(s1, 0x0e71);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x151c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s263(s5, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 280
    * Starting at 0x151c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xe71

    requires s0.stack[6] == 0x1234

    requires s0.stack[10] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe71;
      assert s1.Peek(6) == 0x1234;
      assert s1.Peek(10) == 0x246;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xe71;
      assert s11.Peek(7) == 0x1234;
      assert s11.Peek(11) == 0x246;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s14, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 201
    * Starting at 0xe71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x1234

    requires s0.stack[9] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1234;
      assert s1.Peek(9) == 0x246;
      var s2 := Dup5(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s11, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 229
    * Starting at 0x1234
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1234 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x246

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x246;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s8, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 56
    * Starting at 0x246
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x246 as nat
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

  /** Node 267
    * Segment Id for this node is: 105
    * Starting at 0x50c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x239;
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
      ExecuteFromCFGNode_s268(s11, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 106
    * Starting at 0x51a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x239;
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
      assert s11.Peek(7) == 0x239;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x051a);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s268(s16, gas - 1)
      else
        ExecuteFromCFGNode_s269(s16, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 107
    * Starting at 0x52e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x239

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0x239;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s248(s8, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 51
    * Starting at 0x213
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x213 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x021b);
      var s3 := Push2(s2, 0x0485);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s4, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 99
    * Starting at 0x485
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x485 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x21b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x21b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x21b;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s17, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 52
    * Starting at 0x21b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0228);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11e4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s8, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 224
    * Starting at 0x11e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x228

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x228;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x11f9);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x11f9;
      assert s11.Peek(5) == 0x228;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e25);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s14, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 193
    * Starting at 0xe25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x11f9

    requires s0.stack[6] == 0x228

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11f9;
      assert s1.Peek(6) == 0x228;
      var s2 := Push2(s1, 0x0e2e);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s5, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe2e

    requires s0.stack[4] == 0x11f9

    requires s0.stack[8] == 0x228

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe2e;
      assert s1.Peek(4) == 0x11f9;
      assert s1.Peek(8) == 0x228;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s6, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0xe2e

    requires s0.stack[7] == 0x11f9

    requires s0.stack[11] == 0x228

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0xe2e;
      assert s1.Peek(7) == 0x11f9;
      assert s1.Peek(11) == 0x228;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s11, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe2e

    requires s0.stack[6] == 0x11f9

    requires s0.stack[10] == 0x228

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2e;
      assert s1.Peek(6) == 0x11f9;
      assert s1.Peek(10) == 0x228;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s278(s7, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 194
    * Starting at 0xe2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x11f9

    requires s0.stack[7] == 0x228

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11f9;
      assert s1.Peek(7) == 0x228;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s6, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 225
    * Starting at 0x11f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x228

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x228;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s6, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 53
    * Starting at 0x228
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x228 as nat
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

  /** Node 281
    * Segment Id for this node is: 49
    * Starting at 0x209
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x209 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0211);
      var s3 := Push2(s2, 0x0471);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s4, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 96
    * Starting at 0x471
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x471 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x211;
      var s2 := Push2(s1, 0x0479);
      var s3 := Push2(s2, 0x0bbd);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s4, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 159
    * Starting at 0xbbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x479

    requires s0.stack[1] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x479;
      assert s1.Peek(1) == 0x211;
      var s2 := Push2(s1, 0x0bc5);
      var s3 := Push2(s2, 0x06e6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s4, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 127
    * Starting at 0x6e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0xbc5

    requires s0.stack[1] == 0x479

    requires s0.stack[2] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xbc5;
      assert s1.Peek(1) == 0x479;
      assert s1.Peek(2) == 0x211;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s7, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 160
    * Starting at 0xbc5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x479

    requires s0.stack[2] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x479;
      assert s1.Peek(2) == 0x211;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0be3);
      var s5 := Push2(s4, 0x0485);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s6, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 99
    * Starting at 0x485
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x485 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0xbe3

    requires s0.stack[2] == 0x479

    requires s0.stack[3] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xbe3;
      assert s1.Peek(2) == 0x479;
      assert s1.Peek(3) == 0x211;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0xbe3;
      assert s11.Peek(4) == 0x479;
      assert s11.Peek(5) == 0x211;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s287(s17, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 161
    * Starting at 0xbe3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x479

    requires s0.stack[3] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x479;
      assert s1.Peek(3) == 0x211;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0c39);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s295(s6, gas - 1)
      else
        ExecuteFromCFGNode_s288(s6, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 162
    * Starting at 0xbff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x479

    requires s0.stack[1] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x479;
      assert s1.Peek(2) == 0x211;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c30);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12dc);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s11, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 240
    * Starting at 0x12dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0xc30

    requires s0.stack[2] == 0x479

    requires s0.stack[3] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc30;
      assert s1.Peek(2) == 0x479;
      assert s1.Peek(3) == 0x211;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0xc30;
      assert s11.Peek(5) == 0x479;
      assert s11.Peek(6) == 0x211;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12f5);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1054);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s290(s18, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 212
    * Starting at 0x1054
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x12f5

    requires s0.stack[4] == 0xc30

    requires s0.stack[5] == 0x479

    requires s0.stack[6] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12f5;
      assert s1.Peek(4) == 0xc30;
      assert s1.Peek(5) == 0x479;
      assert s1.Peek(6) == 0x211;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1061);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s291(s7, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x1061

    requires s0.stack[5] == 0x12f5

    requires s0.stack[8] == 0xc30

    requires s0.stack[9] == 0x479

    requires s0.stack[10] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1061;
      assert s1.Peek(5) == 0x12f5;
      assert s1.Peek(8) == 0xc30;
      assert s1.Peek(9) == 0x479;
      assert s1.Peek(10) == 0x211;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1061;
      assert s11.Peek(6) == 0x12f5;
      assert s11.Peek(9) == 0xc30;
      assert s11.Peek(10) == 0x479;
      assert s11.Peek(11) == 0x211;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s15, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 213
    * Starting at 0x1061
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1061 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x12f5

    requires s0.stack[6] == 0xc30

    requires s0.stack[7] == 0x479

    requires s0.stack[8] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12f5;
      assert s1.Peek(6) == 0xc30;
      assert s1.Peek(7) == 0x479;
      assert s1.Peek(8) == 0x211;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x12f5;
      assert s11.Peek(6) == 0xc30;
      assert s11.Peek(7) == 0x479;
      assert s11.Peek(8) == 0x211;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s293(s17, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 241
    * Starting at 0x12f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0xc30

    requires s0.stack[4] == 0x479

    requires s0.stack[5] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc30;
      assert s1.Peek(4) == 0x479;
      assert s1.Peek(5) == 0x211;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s294(s7, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 163
    * Starting at 0xc30
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x479

    requires s0.stack[2] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x479;
      assert s1.Peek(2) == 0x211;
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

  /** Node 295
    * Segment Id for this node is: 164
    * Starting at 0xc39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x479

    requires s0.stack[1] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x479;
      assert s1.Peek(1) == 0x211;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s2, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 97
    * Starting at 0x479
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x479 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x211;
      var s2 := Push2(s1, 0x0483);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x0c3b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s297(s5, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 165
    * Starting at 0xc3b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x483

    requires s0.stack[2] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x483;
      assert s1.Peek(2) == 0x211;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x05);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x483;
      assert s11.Peek(4) == 0x211;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x05);
      var s18 := Push1(s17, 0x00);
      var s19 := Push2(s18, 0x0100);
      var s20 := Exp(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x483;
      assert s21.Peek(7) == 0x211;
      var s22 := SLoad(s21);
      var s23 := Dup2(s22);
      var s24 := Push20(s23, 0xffffffffffffffffffffffffffffffffffffffff);
      var s25 := Mul(s24);
      var s26 := Not(s25);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Dup4(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(7) == 0x483;
      assert s31.Peek(8) == 0x211;
      var s32 := Mul(s31);
      var s33 := Or(s32);
      var s34 := Swap1(s33);
      var s35 := SStore(s34);
      var s36 := Pop(s35);
      var s37 := Dup2(s36);
      var s38 := Push20(s37, 0xffffffffffffffffffffffffffffffffffffffff);
      var s39 := And(s38);
      var s40 := Dup2(s39);
      var s41 := Push20(s40, 0xffffffffffffffffffffffffffffffffffffffff);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s298(s41, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 166
    * Starting at 0xcd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x483

    requires s0.stack[6] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(4) == 0x483;
      assert s1.Peek(5) == 0x211;
      var s2 := Push32(s1, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Swap2(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Log3(s10);
      assert s11.Peek(2) == 0x483;
      assert s11.Peek(3) == 0x211;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s14, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 98
    * Starting at 0x483
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x483 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x211

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x211;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s300(s2, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 50
    * Starting at 0x211
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x211 as nat
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

  /** Node 301
    * Segment Id for this node is: 14
    * Starting at 0x8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x23b872dd);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00c8);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s529(s6, gas - 1)
      else
        ExecuteFromCFGNode_s302(s6, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 15
    * Starting at 0x98
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x015b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s409(s5, gas - 1)
      else
        ExecuteFromCFGNode_s303(s5, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 16
    * Starting at 0xa3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x018b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s400(s5, gas - 1)
      else
        ExecuteFromCFGNode_s304(s5, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 17
    * Starting at 0xae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x39509351);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01a9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s330(s5, gas - 1)
      else
        ExecuteFromCFGNode_s305(s5, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 18
    * Starting at 0xb9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01d9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s307(s5, gas - 1)
      else
        ExecuteFromCFGNode_s306(s5, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 19
    * Starting at 0xc4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00ea);
      assert s1.Peek(0) == 0xea;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 45
    * Starting at 0x1d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01f3);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x01ee);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x1ee;
      assert s11.Peek(3) == 0x1f3;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d35);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s14, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 173
    * Starting at 0xd35
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1ee

    requires s0.stack[3] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ee;
      assert s1.Peek(3) == 0x1f3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d47);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s310(s10, gas - 1)
      else
        ExecuteFromCFGNode_s309(s10, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 174
    * Starting at 0xd43
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1ee

    requires s0.stack[4] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1ee;
      assert s1.Peek(5) == 0x1f3;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 310
    * Segment Id for this node is: 175
    * Starting at 0xd47
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd47 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1ee

    requires s0.stack[4] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1ee;
      assert s1.Peek(4) == 0x1f3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d55);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d0b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s9, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 169
    * Starting at 0xd0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xd55

    requires s0.stack[7] == 0x1ee

    requires s0.stack[8] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd55;
      assert s1.Peek(7) == 0x1ee;
      assert s1.Peek(8) == 0x1f3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d1a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x152d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s312(s10, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 281
    * Starting at 0x152d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd55

    requires s0.stack[10] == 0x1ee

    requires s0.stack[11] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xd55;
      assert s1.Peek(10) == 0x1ee;
      assert s1.Peek(11) == 0x1f3;
      var s2 := Push2(s1, 0x1536);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s313(s5, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1536

    requires s0.stack[3] == 0xd1a

    requires s0.stack[7] == 0xd55

    requires s0.stack[12] == 0x1ee

    requires s0.stack[13] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1536;
      assert s1.Peek(3) == 0xd1a;
      assert s1.Peek(7) == 0xd55;
      assert s1.Peek(12) == 0x1ee;
      assert s1.Peek(13) == 0x1f3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s314(s6, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0x1536

    requires s0.stack[6] == 0xd1a

    requires s0.stack[10] == 0xd55

    requires s0.stack[15] == 0x1ee

    requires s0.stack[16] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0x1536;
      assert s1.Peek(6) == 0xd1a;
      assert s1.Peek(10) == 0xd55;
      assert s1.Peek(15) == 0x1ee;
      assert s1.Peek(16) == 0x1f3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s11, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1536

    requires s0.stack[5] == 0xd1a

    requires s0.stack[9] == 0xd55

    requires s0.stack[14] == 0x1ee

    requires s0.stack[15] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1536;
      assert s1.Peek(5) == 0xd1a;
      assert s1.Peek(9) == 0xd55;
      assert s1.Peek(14) == 0x1ee;
      assert s1.Peek(15) == 0x1f3;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s7, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 282
    * Starting at 0x1536
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xd1a

    requires s0.stack[6] == 0xd55

    requires s0.stack[11] == 0x1ee

    requires s0.stack[12] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xd55;
      assert s1.Peek(11) == 0x1ee;
      assert s1.Peek(12) == 0x1f3;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1541);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s318(s5, gas - 1)
      else
        ExecuteFromCFGNode_s317(s5, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 283
    * Starting at 0x153d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd55

    requires s0.stack[10] == 0x1ee

    requires s0.stack[11] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xd55;
      assert s1.Peek(11) == 0x1ee;
      assert s1.Peek(12) == 0x1f3;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 318
    * Segment Id for this node is: 284
    * Starting at 0x1541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xd55

    requires s0.stack[10] == 0x1ee

    requires s0.stack[11] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xd55;
      assert s1.Peek(10) == 0x1ee;
      assert s1.Peek(11) == 0x1f3;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s319(s3, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 170
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd55

    requires s0.stack[8] == 0x1ee

    requires s0.stack[9] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd55;
      assert s1.Peek(8) == 0x1ee;
      assert s1.Peek(9) == 0x1f3;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s320(s6, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 176
    * Starting at 0xd55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1ee

    requires s0.stack[6] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1ee;
      assert s1.Peek(6) == 0x1f3;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s9, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 46
    * Starting at 0x1ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1f3;
      var s2 := Push2(s1, 0x0429);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s322(s3, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 95
    * Starting at 0x429
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x429 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1f3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1f3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x1f3;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(3) == 0x1f3;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Swap2(s23);
      var s25 := Swap1(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s27, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 47
    * Starting at 0x1f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0200);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x135c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s324(s8, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 248
    * Starting at 0x135c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x200;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1371);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1371;
      assert s11.Peek(5) == 0x200;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x11c6);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s325(s14, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 220
    * Starting at 0x11c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1371

    requires s0.stack[6] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1371;
      assert s1.Peek(6) == 0x200;
      var s2 := Push2(s1, 0x11cf);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s5, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x11cf

    requires s0.stack[4] == 0x1371

    requires s0.stack[8] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11cf;
      assert s1.Peek(4) == 0x1371;
      assert s1.Peek(8) == 0x200;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s327(s9, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 221
    * Starting at 0x11cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1371

    requires s0.stack[7] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1371;
      assert s1.Peek(7) == 0x200;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s6, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 249
    * Starting at 0x1371
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x200;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s329(s6, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 48
    * Starting at 0x200
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x200 as nat
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

  /** Node 330
    * Segment Id for this node is: 41
    * Starting at 0x1a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01c3);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x01be);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x1be;
      assert s11.Peek(3) == 0x1c3;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0de9);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s331(s14, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 188
    * Starting at 0xde9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1be

    requires s0.stack[3] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1be;
      assert s1.Peek(3) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0dfc);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s333(s11, gas - 1)
      else
        ExecuteFromCFGNode_s332(s11, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 189
    * Starting at 0xdf8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1be

    requires s0.stack[5] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1be;
      assert s1.Peek(6) == 0x1c3;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 333
    * Segment Id for this node is: 190
    * Starting at 0xdfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1be

    requires s0.stack[5] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1be;
      assert s1.Peek(5) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0e0a);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d0b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s334(s9, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 169
    * Starting at 0xd0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe0a

    requires s0.stack[8] == 0x1be

    requires s0.stack[9] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe0a;
      assert s1.Peek(8) == 0x1be;
      assert s1.Peek(9) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d1a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x152d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s10, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 281
    * Starting at 0x152d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x1be

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xe0a;
      assert s1.Peek(11) == 0x1be;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Push2(s1, 0x1536);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s5, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1536

    requires s0.stack[3] == 0xd1a

    requires s0.stack[7] == 0xe0a

    requires s0.stack[13] == 0x1be

    requires s0.stack[14] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1536;
      assert s1.Peek(3) == 0xd1a;
      assert s1.Peek(7) == 0xe0a;
      assert s1.Peek(13) == 0x1be;
      assert s1.Peek(14) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s6, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0x1536

    requires s0.stack[6] == 0xd1a

    requires s0.stack[10] == 0xe0a

    requires s0.stack[16] == 0x1be

    requires s0.stack[17] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0x1536;
      assert s1.Peek(6) == 0xd1a;
      assert s1.Peek(10) == 0xe0a;
      assert s1.Peek(16) == 0x1be;
      assert s1.Peek(17) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s338(s11, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1536

    requires s0.stack[5] == 0xd1a

    requires s0.stack[9] == 0xe0a

    requires s0.stack[15] == 0x1be

    requires s0.stack[16] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1536;
      assert s1.Peek(5) == 0xd1a;
      assert s1.Peek(9) == 0xe0a;
      assert s1.Peek(15) == 0x1be;
      assert s1.Peek(16) == 0x1c3;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s7, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 282
    * Starting at 0x1536
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd1a

    requires s0.stack[6] == 0xe0a

    requires s0.stack[12] == 0x1be

    requires s0.stack[13] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xe0a;
      assert s1.Peek(12) == 0x1be;
      assert s1.Peek(13) == 0x1c3;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1541);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s341(s5, gas - 1)
      else
        ExecuteFromCFGNode_s340(s5, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 283
    * Starting at 0x153d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x1be

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xe0a;
      assert s1.Peek(12) == 0x1be;
      assert s1.Peek(13) == 0x1c3;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 341
    * Segment Id for this node is: 284
    * Starting at 0x1541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x1be

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xe0a;
      assert s1.Peek(11) == 0x1be;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s342(s3, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 170
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe0a

    requires s0.stack[9] == 0x1be

    requires s0.stack[10] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe0a;
      assert s1.Peek(9) == 0x1be;
      assert s1.Peek(10) == 0x1c3;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s343(s6, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 191
    * Starting at 0xe0a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1be

    requires s0.stack[7] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1be;
      assert s1.Peek(7) == 0x1c3;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0e1b);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d20);
      assert s11.Peek(0) == 0xd20;
      assert s11.Peek(3) == 0xe1b;
      assert s11.Peek(9) == 0x1be;
      assert s11.Peek(10) == 0x1c3;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s12, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 171
    * Starting at 0xd20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe1b

    requires s0.stack[8] == 0x1be

    requires s0.stack[9] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe1b;
      assert s1.Peek(8) == 0x1be;
      assert s1.Peek(9) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d2f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1544);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s345(s10, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 285
    * Starting at 0x1544
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1544 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x1be

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(5) == 0xe1b;
      assert s1.Peek(11) == 0x1be;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Push2(s1, 0x154d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s346(s5, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x154d

    requires s0.stack[3] == 0xd2f

    requires s0.stack[7] == 0xe1b

    requires s0.stack[13] == 0x1be

    requires s0.stack[14] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x154d;
      assert s1.Peek(3) == 0xd2f;
      assert s1.Peek(7) == 0xe1b;
      assert s1.Peek(13) == 0x1be;
      assert s1.Peek(14) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s9, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 286
    * Starting at 0x154d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd2f

    requires s0.stack[6] == 0xe1b

    requires s0.stack[12] == 0x1be

    requires s0.stack[13] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd2f;
      assert s1.Peek(6) == 0xe1b;
      assert s1.Peek(12) == 0x1be;
      assert s1.Peek(13) == 0x1c3;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1558);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s349(s5, gas - 1)
      else
        ExecuteFromCFGNode_s348(s5, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 287
    * Starting at 0x1554
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1554 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x1be

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd2f;
      assert s1.Peek(6) == 0xe1b;
      assert s1.Peek(12) == 0x1be;
      assert s1.Peek(13) == 0x1c3;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 349
    * Segment Id for this node is: 288
    * Starting at 0x1558
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1558 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x1be

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(5) == 0xe1b;
      assert s1.Peek(11) == 0x1be;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s3, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 172
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe1b

    requires s0.stack[9] == 0x1be

    requires s0.stack[10] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe1b;
      assert s1.Peek(9) == 0x1be;
      assert s1.Peek(10) == 0x1c3;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s351(s6, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 192
    * Starting at 0xe1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1be

    requires s0.stack[7] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1be;
      assert s1.Peek(7) == 0x1c3;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s10, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 42
    * Starting at 0x1be
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c3;
      var s2 := Push2(s1, 0x03f2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s3, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 90
    * Starting at 0x3f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x03fd);
      var s5 := Push2(s4, 0x06e6);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s354(s6, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 127
    * Starting at 0x6e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x3fd

    requires s0.stack[5] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3fd;
      assert s1.Peek(5) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s7, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 91
    * Starting at 0x3fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1c3;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x041e);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x040f);
      var s9 := Dup6(s8);
      var s10 := Dup10(s9);
      var s11 := Push2(s10, 0x05db);
      assert s11.Peek(0) == 0x5db;
      assert s11.Peek(3) == 0x40f;
      assert s11.Peek(7) == 0x41e;
      assert s11.Peek(12) == 0x1c3;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s12, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 119
    * Starting at 0x5db
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x40f

    requires s0.stack[6] == 0x41e

    requires s0.stack[11] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x40f;
      assert s1.Peek(6) == 0x41e;
      assert s1.Peek(11) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x40f;
      assert s11.Peek(9) == 0x41e;
      assert s11.Peek(14) == 0x1c3;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x40f;
      assert s21.Peek(9) == 0x41e;
      assert s21.Peek(14) == 0x1c3;
      var s22 := Dup4(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x40f;
      assert s31.Peek(9) == 0x41e;
      assert s31.Peek(14) == 0x1c3;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s357(s41, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 120
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x40f

    requires s0.stack[7] == 0x41e

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x40f;
      assert s1.Peek(7) == 0x41e;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s358(s4, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 92
    * Starting at 0x40f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x41e

    requires s0.stack[9] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x41e;
      assert s1.Peek(9) == 0x1c3;
      var s2 := Push2(s1, 0x0419);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x13ae);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s359(s6, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 254
    * Starting at 0x13ae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x419

    requires s0.stack[5] == 0x41e

    requires s0.stack[10] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x419;
      assert s1.Peek(5) == 0x41e;
      assert s1.Peek(10) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x13b9);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1442);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s360(s6, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x13b9

    requires s0.stack[5] == 0x419

    requires s0.stack[8] == 0x41e

    requires s0.stack[13] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13b9;
      assert s1.Peek(5) == 0x419;
      assert s1.Peek(8) == 0x41e;
      assert s1.Peek(13) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s361(s9, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 255
    * Starting at 0x13b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x419

    requires s0.stack[7] == 0x41e

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x419;
      assert s1.Peek(7) == 0x41e;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x13c4);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x1442);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s7, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x13c4

    requires s0.stack[5] == 0x419

    requires s0.stack[8] == 0x41e

    requires s0.stack[13] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13c4;
      assert s1.Peek(5) == 0x419;
      assert s1.Peek(8) == 0x41e;
      assert s1.Peek(13) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s9, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 256
    * Starting at 0x13c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x419

    requires s0.stack[7] == 0x41e

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x419;
      assert s1.Peek(7) == 0x41e;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x13f9);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s366(s11, gas - 1)
      else
        ExecuteFromCFGNode_s364(s11, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 257
    * Starting at 0x13f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x419

    requires s0.stack[6] == 0x41e

    requires s0.stack[11] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x13f8);
      assert s1.Peek(0) == 0x13f8;
      assert s1.Peek(4) == 0x419;
      assert s1.Peek(7) == 0x41e;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Push2(s1, 0x14be);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s3, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 278
    * Starting at 0x14be
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x13f8

    requires s0.stack[4] == 0x419

    requires s0.stack[7] == 0x41e

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x13f8;
      assert s1.Peek(4) == 0x419;
      assert s1.Peek(7) == 0x41e;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 366
    * Segment Id for this node is: 259
    * Starting at 0x13f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x419

    requires s0.stack[6] == 0x41e

    requires s0.stack[11] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x419;
      assert s1.Peek(6) == 0x41e;
      assert s1.Peek(11) == 0x1c3;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s367(s11, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 93
    * Starting at 0x419
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x419 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x41e

    requires s0.stack[8] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x41e;
      assert s1.Peek(8) == 0x1c3;
      var s2 := Push2(s1, 0x06ee);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s3, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 128
    * Starting at 0x6ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x41e

    requires s0.stack[8] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x41e;
      assert s1.Peek(8) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x075e);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s376(s11, gas - 1)
      else
        ExecuteFromCFGNode_s369(s11, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 129
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x41e

    requires s0.stack[8] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x41e;
      assert s1.Peek(9) == 0x1c3;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0755);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x131c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s11, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 244
    * Starting at 0x131c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x755

    requires s0.stack[5] == 0x41e

    requires s0.stack[10] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x755;
      assert s1.Peek(5) == 0x41e;
      assert s1.Peek(10) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x755;
      assert s11.Peek(8) == 0x41e;
      assert s11.Peek(13) == 0x1c3;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1335);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10fa);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s371(s18, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 216
    * Starting at 0x10fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1335

    requires s0.stack[4] == 0x755

    requires s0.stack[8] == 0x41e

    requires s0.stack[13] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1335;
      assert s1.Peek(4) == 0x755;
      assert s1.Peek(8) == 0x41e;
      assert s1.Peek(13) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1107);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s7, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1107

    requires s0.stack[5] == 0x1335

    requires s0.stack[8] == 0x755

    requires s0.stack[12] == 0x41e

    requires s0.stack[17] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1107;
      assert s1.Peek(5) == 0x1335;
      assert s1.Peek(8) == 0x755;
      assert s1.Peek(12) == 0x41e;
      assert s1.Peek(17) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1107;
      assert s11.Peek(6) == 0x1335;
      assert s11.Peek(9) == 0x755;
      assert s11.Peek(13) == 0x41e;
      assert s11.Peek(18) == 0x1c3;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s15, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 217
    * Starting at 0x1107
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1107 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1335

    requires s0.stack[6] == 0x755

    requires s0.stack[10] == 0x41e

    requires s0.stack[15] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1335;
      assert s1.Peek(6) == 0x755;
      assert s1.Peek(10) == 0x41e;
      assert s1.Peek(15) == 0x1c3;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1335;
      assert s11.Peek(8) == 0x755;
      assert s11.Peek(12) == 0x41e;
      assert s11.Peek(17) == 0x1c3;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1335;
      assert s21.Peek(4) == 0x755;
      assert s21.Peek(8) == 0x41e;
      assert s21.Peek(13) == 0x1c3;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s374(s22, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 245
    * Starting at 0x1335
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1335 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x755

    requires s0.stack[7] == 0x41e

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x755;
      assert s1.Peek(7) == 0x41e;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s7, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 130
    * Starting at 0x755
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x755 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x41e

    requires s0.stack[9] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x41e;
      assert s1.Peek(9) == 0x1c3;
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

  /** Node 376
    * Segment Id for this node is: 131
    * Starting at 0x75e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x41e

    requires s0.stack[8] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x41e;
      assert s1.Peek(8) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x07ce);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s384(s11, gas - 1)
      else
        ExecuteFromCFGNode_s377(s11, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 132
    * Starting at 0x794
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x794 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x41e

    requires s0.stack[8] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x41e;
      assert s1.Peek(9) == 0x1c3;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x07c5);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x127c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s378(s11, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 234
    * Starting at 0x127c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x7c5

    requires s0.stack[5] == 0x41e

    requires s0.stack[10] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7c5;
      assert s1.Peek(5) == 0x41e;
      assert s1.Peek(10) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x7c5;
      assert s11.Peek(8) == 0x41e;
      assert s11.Peek(13) == 0x1c3;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1295);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0f48);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s379(s18, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 206
    * Starting at 0xf48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1295

    requires s0.stack[4] == 0x7c5

    requires s0.stack[8] == 0x41e

    requires s0.stack[13] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1295;
      assert s1.Peek(4) == 0x7c5;
      assert s1.Peek(8) == 0x41e;
      assert s1.Peek(13) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f55);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s7, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xf55

    requires s0.stack[5] == 0x1295

    requires s0.stack[8] == 0x7c5

    requires s0.stack[12] == 0x41e

    requires s0.stack[17] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf55;
      assert s1.Peek(5) == 0x1295;
      assert s1.Peek(8) == 0x7c5;
      assert s1.Peek(12) == 0x41e;
      assert s1.Peek(17) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xf55;
      assert s11.Peek(6) == 0x1295;
      assert s11.Peek(9) == 0x7c5;
      assert s11.Peek(13) == 0x41e;
      assert s11.Peek(18) == 0x1c3;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s381(s15, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 207
    * Starting at 0xf55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1295

    requires s0.stack[6] == 0x7c5

    requires s0.stack[10] == 0x41e

    requires s0.stack[15] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1295;
      assert s1.Peek(6) == 0x7c5;
      assert s1.Peek(10) == 0x41e;
      assert s1.Peek(15) == 0x1c3;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1295;
      assert s11.Peek(8) == 0x7c5;
      assert s11.Peek(12) == 0x41e;
      assert s11.Peek(17) == 0x1c3;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1295;
      assert s21.Peek(4) == 0x7c5;
      assert s21.Peek(8) == 0x41e;
      assert s21.Peek(13) == 0x1c3;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s22, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 235
    * Starting at 0x1295
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x7c5

    requires s0.stack[7] == 0x41e

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7c5;
      assert s1.Peek(7) == 0x41e;
      assert s1.Peek(12) == 0x1c3;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s7, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 133
    * Starting at 0x7c5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x41e

    requires s0.stack[9] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x41e;
      assert s1.Peek(9) == 0x1c3;
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

  /** Node 384
    * Segment Id for this node is: 134
    * Starting at 0x7ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x41e

    requires s0.stack[8] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x41e;
      assert s1.Peek(8) == 0x1c3;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x41e;
      assert s11.Peek(11) == 0x1c3;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(6) == 0x41e;
      assert s21.Peek(11) == 0x1c3;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x41e;
      assert s31.Peek(11) == 0x1c3;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s385(s41, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 135
    * Starting at 0x850
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x850 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x41e

    requires s0.stack[8] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x41e;
      assert s1.Peek(9) == 0x1c3;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08ac);
      assert s11.Peek(0) == 0x8ac;
      assert s11.Peek(9) == 0x41e;
      assert s11.Peek(14) == 0x1c3;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x135c);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s15, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 248
    * Starting at 0x135c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x8ac

    requires s0.stack[9] == 0x41e

    requires s0.stack[14] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8ac;
      assert s1.Peek(9) == 0x41e;
      assert s1.Peek(14) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1371);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1371;
      assert s11.Peek(5) == 0x8ac;
      assert s11.Peek(12) == 0x41e;
      assert s11.Peek(17) == 0x1c3;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x11c6);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s387(s14, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 220
    * Starting at 0x11c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x1371

    requires s0.stack[6] == 0x8ac

    requires s0.stack[13] == 0x41e

    requires s0.stack[18] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1371;
      assert s1.Peek(6) == 0x8ac;
      assert s1.Peek(13) == 0x41e;
      assert s1.Peek(18) == 0x1c3;
      var s2 := Push2(s1, 0x11cf);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s388(s5, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x11cf

    requires s0.stack[4] == 0x1371

    requires s0.stack[8] == 0x8ac

    requires s0.stack[15] == 0x41e

    requires s0.stack[20] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11cf;
      assert s1.Peek(4) == 0x1371;
      assert s1.Peek(8) == 0x8ac;
      assert s1.Peek(15) == 0x41e;
      assert s1.Peek(20) == 0x1c3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s389(s9, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 221
    * Starting at 0x11cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x1371

    requires s0.stack[7] == 0x8ac

    requires s0.stack[14] == 0x41e

    requires s0.stack[19] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1371;
      assert s1.Peek(7) == 0x8ac;
      assert s1.Peek(14) == 0x41e;
      assert s1.Peek(19) == 0x1c3;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s390(s6, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 249
    * Starting at 0x1371
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x8ac

    requires s0.stack[10] == 0x41e

    requires s0.stack[15] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8ac;
      assert s1.Peek(10) == 0x41e;
      assert s1.Peek(15) == 0x1c3;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s391(s6, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 136
    * Starting at 0x8ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x41e

    requires s0.stack[12] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x41e;
      assert s1.Peek(12) == 0x1c3;
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
      assert s11.Peek(0) == 0x41e;
      assert s11.Peek(5) == 0x1c3;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s392(s12, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 94
    * Starting at 0x41e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1c3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1c3;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s10, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 43
    * Starting at 0x1c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01d0);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11ff);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s8, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 226
    * Starting at 0x11ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1d0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1214);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1214;
      assert s11.Peek(5) == 0x1d0;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e34);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s395(s14, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 195
    * Starting at 0xe34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1214

    requires s0.stack[6] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1214;
      assert s1.Peek(6) == 0x1d0;
      var s2 := Push2(s1, 0x0e3d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1416);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s5, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 262
    * Starting at 0x1416
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1416 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe3d

    requires s0.stack[4] == 0x1214

    requires s0.stack[8] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe3d;
      assert s1.Peek(4) == 0x1214;
      assert s1.Peek(8) == 0x1d0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s397(s11, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 196
    * Starting at 0xe3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1214

    requires s0.stack[7] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1214;
      assert s1.Peek(7) == 0x1d0;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s6, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 227
    * Starting at 0x1214
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1214 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1d0;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s399(s6, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 44
    * Starting at 0x1d0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d0 as nat
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

  /** Node 400
    * Segment Id for this node is: 38
    * Starting at 0x18b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0193);
      var s3 := Push2(s2, 0x03e9);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s401(s4, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 89
    * Starting at 0x3e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x193

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x193;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x12);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s402(s7, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 39
    * Starting at 0x193
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x193 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01a0);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1377);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s403(s8, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 250
    * Starting at 0x1377
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1377 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1a0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1a0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x138c);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x138c;
      assert s11.Peek(5) == 0x1a0;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x11d5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s14, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 222
    * Starting at 0x11d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x138c

    requires s0.stack[6] == 0x1a0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x138c;
      assert s1.Peek(6) == 0x1a0;
      var s2 := Push2(s1, 0x11de);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x144c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s5, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 265
    * Starting at 0x144c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x144c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x11de

    requires s0.stack[4] == 0x138c

    requires s0.stack[8] == 0x1a0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11de;
      assert s1.Peek(4) == 0x138c;
      assert s1.Peek(8) == 0x1a0;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0xff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s11, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 223
    * Starting at 0x11de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x138c

    requires s0.stack[7] == 0x1a0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x138c;
      assert s1.Peek(7) == 0x1a0;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s407(s6, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 251
    * Starting at 0x138c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x138c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1a0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1a0;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s6, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 40
    * Starting at 0x1a0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a0 as nat
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

  /** Node 409
    * Segment Id for this node is: 34
    * Starting at 0x15b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0175);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0170);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x170;
      assert s11.Peek(3) == 0x175;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d9a);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s410(s14, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 182
    * Starting at 0xd9a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x170

    requires s0.stack[3] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x170;
      assert s1.Peek(3) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0daf);
      assert s11.Peek(0) == 0xdaf;
      assert s11.Peek(7) == 0x170;
      assert s11.Peek(8) == 0x175;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s412(s12, gas - 1)
      else
        ExecuteFromCFGNode_s411(s12, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 183
    * Starting at 0xdab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x170

    requires s0.stack[6] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x170;
      assert s1.Peek(7) == 0x175;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 412
    * Segment Id for this node is: 184
    * Starting at 0xdaf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x170

    requires s0.stack[6] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x170;
      assert s1.Peek(6) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0dbd);
      var s4 := Dup7(s3);
      var s5 := Dup3(s4);
      var s6 := Dup8(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d0b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s413(s9, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 169
    * Starting at 0xd0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xdbd

    requires s0.stack[9] == 0x170

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdbd;
      assert s1.Peek(9) == 0x170;
      assert s1.Peek(10) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d1a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x152d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s414(s10, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 281
    * Starting at 0x152d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xdbd

    requires s0.stack[12] == 0x170

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xdbd;
      assert s1.Peek(12) == 0x170;
      assert s1.Peek(13) == 0x175;
      var s2 := Push2(s1, 0x1536);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s5, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x1536

    requires s0.stack[3] == 0xd1a

    requires s0.stack[7] == 0xdbd

    requires s0.stack[14] == 0x170

    requires s0.stack[15] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1536;
      assert s1.Peek(3) == 0xd1a;
      assert s1.Peek(7) == 0xdbd;
      assert s1.Peek(14) == 0x170;
      assert s1.Peek(15) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s416(s6, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0x1536

    requires s0.stack[6] == 0xd1a

    requires s0.stack[10] == 0xdbd

    requires s0.stack[17] == 0x170

    requires s0.stack[18] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0x1536;
      assert s1.Peek(6) == 0xd1a;
      assert s1.Peek(10) == 0xdbd;
      assert s1.Peek(17) == 0x170;
      assert s1.Peek(18) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s417(s11, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x1536

    requires s0.stack[5] == 0xd1a

    requires s0.stack[9] == 0xdbd

    requires s0.stack[16] == 0x170

    requires s0.stack[17] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1536;
      assert s1.Peek(5) == 0xd1a;
      assert s1.Peek(9) == 0xdbd;
      assert s1.Peek(16) == 0x170;
      assert s1.Peek(17) == 0x175;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s418(s7, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 282
    * Starting at 0x1536
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xd1a

    requires s0.stack[6] == 0xdbd

    requires s0.stack[13] == 0x170

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xdbd;
      assert s1.Peek(13) == 0x170;
      assert s1.Peek(14) == 0x175;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1541);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s420(s5, gas - 1)
      else
        ExecuteFromCFGNode_s419(s5, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 283
    * Starting at 0x153d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xdbd

    requires s0.stack[12] == 0x170

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xdbd;
      assert s1.Peek(13) == 0x170;
      assert s1.Peek(14) == 0x175;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 420
    * Segment Id for this node is: 284
    * Starting at 0x1541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xdbd

    requires s0.stack[12] == 0x170

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xdbd;
      assert s1.Peek(12) == 0x170;
      assert s1.Peek(13) == 0x175;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s3, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 170
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xdbd

    requires s0.stack[10] == 0x170

    requires s0.stack[11] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdbd;
      assert s1.Peek(10) == 0x170;
      assert s1.Peek(11) == 0x175;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s422(s6, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 185
    * Starting at 0xdbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x170

    requires s0.stack[8] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x170;
      assert s1.Peek(8) == 0x175;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0dce);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d0b);
      assert s11.Peek(0) == 0xd0b;
      assert s11.Peek(3) == 0xdce;
      assert s11.Peek(10) == 0x170;
      assert s11.Peek(11) == 0x175;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s423(s12, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 169
    * Starting at 0xd0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xdce

    requires s0.stack[9] == 0x170

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdce;
      assert s1.Peek(9) == 0x170;
      assert s1.Peek(10) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d1a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x152d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s424(s10, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 281
    * Starting at 0x152d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xdce

    requires s0.stack[12] == 0x170

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xdce;
      assert s1.Peek(12) == 0x170;
      assert s1.Peek(13) == 0x175;
      var s2 := Push2(s1, 0x1536);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s425(s5, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x1536

    requires s0.stack[3] == 0xd1a

    requires s0.stack[7] == 0xdce

    requires s0.stack[14] == 0x170

    requires s0.stack[15] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1536;
      assert s1.Peek(3) == 0xd1a;
      assert s1.Peek(7) == 0xdce;
      assert s1.Peek(14) == 0x170;
      assert s1.Peek(15) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s426(s6, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0x1536

    requires s0.stack[6] == 0xd1a

    requires s0.stack[10] == 0xdce

    requires s0.stack[17] == 0x170

    requires s0.stack[18] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0x1536;
      assert s1.Peek(6) == 0xd1a;
      assert s1.Peek(10) == 0xdce;
      assert s1.Peek(17) == 0x170;
      assert s1.Peek(18) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s427(s11, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x1536

    requires s0.stack[5] == 0xd1a

    requires s0.stack[9] == 0xdce

    requires s0.stack[16] == 0x170

    requires s0.stack[17] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1536;
      assert s1.Peek(5) == 0xd1a;
      assert s1.Peek(9) == 0xdce;
      assert s1.Peek(16) == 0x170;
      assert s1.Peek(17) == 0x175;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s428(s7, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 282
    * Starting at 0x1536
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xd1a

    requires s0.stack[6] == 0xdce

    requires s0.stack[13] == 0x170

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xdce;
      assert s1.Peek(13) == 0x170;
      assert s1.Peek(14) == 0x175;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1541);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s430(s5, gas - 1)
      else
        ExecuteFromCFGNode_s429(s5, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 283
    * Starting at 0x153d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xdce

    requires s0.stack[12] == 0x170

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xdce;
      assert s1.Peek(13) == 0x170;
      assert s1.Peek(14) == 0x175;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 430
    * Segment Id for this node is: 284
    * Starting at 0x1541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xdce

    requires s0.stack[12] == 0x170

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xdce;
      assert s1.Peek(12) == 0x170;
      assert s1.Peek(13) == 0x175;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s431(s3, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 170
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xdce

    requires s0.stack[10] == 0x170

    requires s0.stack[11] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdce;
      assert s1.Peek(10) == 0x170;
      assert s1.Peek(11) == 0x175;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s432(s6, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 186
    * Starting at 0xdce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x170

    requires s0.stack[8] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x170;
      assert s1.Peek(8) == 0x175;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Push2(s5, 0x0ddf);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d20);
      assert s11.Peek(0) == 0xd20;
      assert s11.Peek(3) == 0xddf;
      assert s11.Peek(10) == 0x170;
      assert s11.Peek(11) == 0x175;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s433(s12, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 171
    * Starting at 0xd20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xddf

    requires s0.stack[9] == 0x170

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xddf;
      assert s1.Peek(9) == 0x170;
      assert s1.Peek(10) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d2f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1544);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s434(s10, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 285
    * Starting at 0x1544
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1544 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xddf

    requires s0.stack[12] == 0x170

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(5) == 0xddf;
      assert s1.Peek(12) == 0x170;
      assert s1.Peek(13) == 0x175;
      var s2 := Push2(s1, 0x154d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s435(s5, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x154d

    requires s0.stack[3] == 0xd2f

    requires s0.stack[7] == 0xddf

    requires s0.stack[14] == 0x170

    requires s0.stack[15] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x154d;
      assert s1.Peek(3) == 0xd2f;
      assert s1.Peek(7) == 0xddf;
      assert s1.Peek(14) == 0x170;
      assert s1.Peek(15) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s436(s9, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 286
    * Starting at 0x154d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xd2f

    requires s0.stack[6] == 0xddf

    requires s0.stack[13] == 0x170

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd2f;
      assert s1.Peek(6) == 0xddf;
      assert s1.Peek(13) == 0x170;
      assert s1.Peek(14) == 0x175;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1558);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s438(s5, gas - 1)
      else
        ExecuteFromCFGNode_s437(s5, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 287
    * Starting at 0x1554
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1554 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xddf

    requires s0.stack[12] == 0x170

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd2f;
      assert s1.Peek(6) == 0xddf;
      assert s1.Peek(13) == 0x170;
      assert s1.Peek(14) == 0x175;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 438
    * Segment Id for this node is: 288
    * Starting at 0x1558
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1558 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xddf

    requires s0.stack[12] == 0x170

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(5) == 0xddf;
      assert s1.Peek(12) == 0x170;
      assert s1.Peek(13) == 0x175;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s3, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 172
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xddf

    requires s0.stack[10] == 0x170

    requires s0.stack[11] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xddf;
      assert s1.Peek(10) == 0x170;
      assert s1.Peek(11) == 0x175;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s440(s6, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 187
    * Starting at 0xddf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xddf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x170

    requires s0.stack[8] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x170;
      assert s1.Peek(8) == 0x175;
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
      ExecuteFromCFGNode_s441(s10, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 35
    * Starting at 0x170
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x170 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x175;
      var s2 := Push2(s1, 0x03ba);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s3, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 85
    * Starting at 0x3ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x03c5);
      var s5 := Push2(s4, 0x06e6);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s6, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 127
    * Starting at 0x6e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x3c5

    requires s0.stack[6] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c5;
      assert s1.Peek(6) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s444(s7, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 86
    * Starting at 0x3c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x175;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x03d2);
      var s5 := Dup6(s4);
      var s6 := Dup3(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x08b9);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s9, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 137
    * Starting at 0x8b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3d2

    requires s0.stack[9] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d2;
      assert s1.Peek(9) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x08c5);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x05db);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s7, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 119
    * Starting at 0x5db
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x8c5

    requires s0.stack[7] == 0x3d2

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8c5;
      assert s1.Peek(7) == 0x3d2;
      assert s1.Peek(13) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x8c5;
      assert s11.Peek(10) == 0x3d2;
      assert s11.Peek(16) == 0x175;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(5) == 0x8c5;
      assert s21.Peek(10) == 0x3d2;
      assert s21.Peek(16) == 0x175;
      var s22 := Dup4(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x8c5;
      assert s31.Peek(10) == 0x3d2;
      assert s31.Peek(16) == 0x175;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s447(s41, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 120
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x8c5

    requires s0.stack[8] == 0x3d2

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x8c5;
      assert s1.Peek(8) == 0x3d2;
      assert s1.Peek(14) == 0x175;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s448(s4, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 138
    * Starting at 0x8c5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x3d2

    requires s0.stack[11] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3d2;
      assert s1.Peek(11) == 0x175;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x093f);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s483(s8, gas - 1)
      else
        ExecuteFromCFGNode_s449(s8, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 139
    * Starting at 0x8ef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3d2

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x3d2;
      assert s1.Peek(11) == 0x175;
      var s2 := Dup2(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0931);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s457(s6, gas - 1)
      else
        ExecuteFromCFGNode_s450(s6, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 140
    * Starting at 0x8f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3d2

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x3d2;
      assert s1.Peek(11) == 0x175;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0928);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x129c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s451(s11, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 236
    * Starting at 0x129c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x928

    requires s0.stack[6] == 0x3d2

    requires s0.stack[12] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x928;
      assert s1.Peek(6) == 0x3d2;
      assert s1.Peek(12) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x928;
      assert s11.Peek(9) == 0x3d2;
      assert s11.Peek(15) == 0x175;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12b5);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0fae);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s18, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 208
    * Starting at 0xfae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x12b5

    requires s0.stack[4] == 0x928

    requires s0.stack[9] == 0x3d2

    requires s0.stack[15] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12b5;
      assert s1.Peek(4) == 0x928;
      assert s1.Peek(9) == 0x3d2;
      assert s1.Peek(15) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0fbb);
      var s4 := Push1(s3, 0x1d);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s453(s7, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xfbb

    requires s0.stack[5] == 0x12b5

    requires s0.stack[8] == 0x928

    requires s0.stack[13] == 0x3d2

    requires s0.stack[19] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfbb;
      assert s1.Peek(5) == 0x12b5;
      assert s1.Peek(8) == 0x928;
      assert s1.Peek(13) == 0x3d2;
      assert s1.Peek(19) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xfbb;
      assert s11.Peek(6) == 0x12b5;
      assert s11.Peek(9) == 0x928;
      assert s11.Peek(14) == 0x3d2;
      assert s11.Peek(20) == 0x175;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s454(s15, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 209
    * Starting at 0xfbb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x12b5

    requires s0.stack[6] == 0x928

    requires s0.stack[11] == 0x3d2

    requires s0.stack[17] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12b5;
      assert s1.Peek(6) == 0x928;
      assert s1.Peek(11) == 0x3d2;
      assert s1.Peek(17) == 0x175;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a20696e73756666696369656e7420616c6c6f77616e6365000000);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x12b5;
      assert s11.Peek(6) == 0x928;
      assert s11.Peek(11) == 0x3d2;
      assert s11.Peek(17) == 0x175;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s455(s17, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 237
    * Starting at 0x12b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x928

    requires s0.stack[8] == 0x3d2

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x928;
      assert s1.Peek(8) == 0x3d2;
      assert s1.Peek(14) == 0x175;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s456(s7, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 141
    * Starting at 0x928
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x928 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x3d2

    requires s0.stack[11] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3d2;
      assert s1.Peek(11) == 0x175;
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

  /** Node 457
    * Segment Id for this node is: 142
    * Starting at 0x931
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x931 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3d2

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3d2;
      assert s1.Peek(10) == 0x175;
      var s2 := Push2(s1, 0x093e);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x06ee);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s458(s9, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 128
    * Starting at 0x6ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x93e

    requires s0.stack[8] == 0x3d2

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x93e;
      assert s1.Peek(8) == 0x3d2;
      assert s1.Peek(14) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x075e);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s466(s11, gas - 1)
      else
        ExecuteFromCFGNode_s459(s11, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 129
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x93e

    requires s0.stack[8] == 0x3d2

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x93e;
      assert s1.Peek(9) == 0x3d2;
      assert s1.Peek(15) == 0x175;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0755);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x131c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s11, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 244
    * Starting at 0x131c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x755

    requires s0.stack[5] == 0x93e

    requires s0.stack[10] == 0x3d2

    requires s0.stack[16] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x755;
      assert s1.Peek(5) == 0x93e;
      assert s1.Peek(10) == 0x3d2;
      assert s1.Peek(16) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x755;
      assert s11.Peek(8) == 0x93e;
      assert s11.Peek(13) == 0x3d2;
      assert s11.Peek(19) == 0x175;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1335);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10fa);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s18, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 216
    * Starting at 0x10fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1335

    requires s0.stack[4] == 0x755

    requires s0.stack[8] == 0x93e

    requires s0.stack[13] == 0x3d2

    requires s0.stack[19] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1335;
      assert s1.Peek(4) == 0x755;
      assert s1.Peek(8) == 0x93e;
      assert s1.Peek(13) == 0x3d2;
      assert s1.Peek(19) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1107);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s7, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x1107

    requires s0.stack[5] == 0x1335

    requires s0.stack[8] == 0x755

    requires s0.stack[12] == 0x93e

    requires s0.stack[17] == 0x3d2

    requires s0.stack[23] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1107;
      assert s1.Peek(5) == 0x1335;
      assert s1.Peek(8) == 0x755;
      assert s1.Peek(12) == 0x93e;
      assert s1.Peek(17) == 0x3d2;
      assert s1.Peek(23) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1107;
      assert s11.Peek(6) == 0x1335;
      assert s11.Peek(9) == 0x755;
      assert s11.Peek(13) == 0x93e;
      assert s11.Peek(18) == 0x3d2;
      assert s11.Peek(24) == 0x175;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s463(s15, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 217
    * Starting at 0x1107
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1107 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x1335

    requires s0.stack[6] == 0x755

    requires s0.stack[10] == 0x93e

    requires s0.stack[15] == 0x3d2

    requires s0.stack[21] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1335;
      assert s1.Peek(6) == 0x755;
      assert s1.Peek(10) == 0x93e;
      assert s1.Peek(15) == 0x3d2;
      assert s1.Peek(21) == 0x175;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1335;
      assert s11.Peek(8) == 0x755;
      assert s11.Peek(12) == 0x93e;
      assert s11.Peek(17) == 0x3d2;
      assert s11.Peek(23) == 0x175;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1335;
      assert s21.Peek(4) == 0x755;
      assert s21.Peek(8) == 0x93e;
      assert s21.Peek(13) == 0x3d2;
      assert s21.Peek(19) == 0x175;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s22, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 245
    * Starting at 0x1335
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1335 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x755

    requires s0.stack[7] == 0x93e

    requires s0.stack[12] == 0x3d2

    requires s0.stack[18] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x755;
      assert s1.Peek(7) == 0x93e;
      assert s1.Peek(12) == 0x3d2;
      assert s1.Peek(18) == 0x175;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s465(s7, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 130
    * Starting at 0x755
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x755 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x93e

    requires s0.stack[9] == 0x3d2

    requires s0.stack[15] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x93e;
      assert s1.Peek(9) == 0x3d2;
      assert s1.Peek(15) == 0x175;
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

  /** Node 466
    * Segment Id for this node is: 131
    * Starting at 0x75e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x93e

    requires s0.stack[8] == 0x3d2

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x93e;
      assert s1.Peek(8) == 0x3d2;
      assert s1.Peek(14) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x07ce);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s474(s11, gas - 1)
      else
        ExecuteFromCFGNode_s467(s11, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 132
    * Starting at 0x794
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x794 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x93e

    requires s0.stack[8] == 0x3d2

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x93e;
      assert s1.Peek(9) == 0x3d2;
      assert s1.Peek(15) == 0x175;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x07c5);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x127c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s468(s11, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 234
    * Starting at 0x127c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x7c5

    requires s0.stack[5] == 0x93e

    requires s0.stack[10] == 0x3d2

    requires s0.stack[16] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7c5;
      assert s1.Peek(5) == 0x93e;
      assert s1.Peek(10) == 0x3d2;
      assert s1.Peek(16) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x7c5;
      assert s11.Peek(8) == 0x93e;
      assert s11.Peek(13) == 0x3d2;
      assert s11.Peek(19) == 0x175;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1295);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0f48);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s18, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 206
    * Starting at 0xf48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1295

    requires s0.stack[4] == 0x7c5

    requires s0.stack[8] == 0x93e

    requires s0.stack[13] == 0x3d2

    requires s0.stack[19] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1295;
      assert s1.Peek(4) == 0x7c5;
      assert s1.Peek(8) == 0x93e;
      assert s1.Peek(13) == 0x3d2;
      assert s1.Peek(19) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f55);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s470(s7, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xf55

    requires s0.stack[5] == 0x1295

    requires s0.stack[8] == 0x7c5

    requires s0.stack[12] == 0x93e

    requires s0.stack[17] == 0x3d2

    requires s0.stack[23] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf55;
      assert s1.Peek(5) == 0x1295;
      assert s1.Peek(8) == 0x7c5;
      assert s1.Peek(12) == 0x93e;
      assert s1.Peek(17) == 0x3d2;
      assert s1.Peek(23) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xf55;
      assert s11.Peek(6) == 0x1295;
      assert s11.Peek(9) == 0x7c5;
      assert s11.Peek(13) == 0x93e;
      assert s11.Peek(18) == 0x3d2;
      assert s11.Peek(24) == 0x175;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s471(s15, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 207
    * Starting at 0xf55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x1295

    requires s0.stack[6] == 0x7c5

    requires s0.stack[10] == 0x93e

    requires s0.stack[15] == 0x3d2

    requires s0.stack[21] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1295;
      assert s1.Peek(6) == 0x7c5;
      assert s1.Peek(10) == 0x93e;
      assert s1.Peek(15) == 0x3d2;
      assert s1.Peek(21) == 0x175;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1295;
      assert s11.Peek(8) == 0x7c5;
      assert s11.Peek(12) == 0x93e;
      assert s11.Peek(17) == 0x3d2;
      assert s11.Peek(23) == 0x175;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1295;
      assert s21.Peek(4) == 0x7c5;
      assert s21.Peek(8) == 0x93e;
      assert s21.Peek(13) == 0x3d2;
      assert s21.Peek(19) == 0x175;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s22, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 235
    * Starting at 0x1295
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x7c5

    requires s0.stack[7] == 0x93e

    requires s0.stack[12] == 0x3d2

    requires s0.stack[18] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7c5;
      assert s1.Peek(7) == 0x93e;
      assert s1.Peek(12) == 0x3d2;
      assert s1.Peek(18) == 0x175;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s473(s7, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 133
    * Starting at 0x7c5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x93e

    requires s0.stack[9] == 0x3d2

    requires s0.stack[15] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x93e;
      assert s1.Peek(9) == 0x3d2;
      assert s1.Peek(15) == 0x175;
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

  /** Node 474
    * Segment Id for this node is: 134
    * Starting at 0x7ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x93e

    requires s0.stack[8] == 0x3d2

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x93e;
      assert s1.Peek(8) == 0x3d2;
      assert s1.Peek(14) == 0x175;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x93e;
      assert s11.Peek(11) == 0x3d2;
      assert s11.Peek(17) == 0x175;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(6) == 0x93e;
      assert s21.Peek(11) == 0x3d2;
      assert s21.Peek(17) == 0x175;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x93e;
      assert s31.Peek(11) == 0x3d2;
      assert s31.Peek(17) == 0x175;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s475(s41, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 135
    * Starting at 0x850
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x850 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x93e

    requires s0.stack[8] == 0x3d2

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x93e;
      assert s1.Peek(9) == 0x3d2;
      assert s1.Peek(15) == 0x175;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08ac);
      assert s11.Peek(0) == 0x8ac;
      assert s11.Peek(9) == 0x93e;
      assert s11.Peek(14) == 0x3d2;
      assert s11.Peek(20) == 0x175;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x135c);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s15, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 248
    * Starting at 0x135c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x8ac

    requires s0.stack[9] == 0x93e

    requires s0.stack[14] == 0x3d2

    requires s0.stack[20] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8ac;
      assert s1.Peek(9) == 0x93e;
      assert s1.Peek(14) == 0x3d2;
      assert s1.Peek(20) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1371);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1371;
      assert s11.Peek(5) == 0x8ac;
      assert s11.Peek(12) == 0x93e;
      assert s11.Peek(17) == 0x3d2;
      assert s11.Peek(23) == 0x175;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x11c6);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s477(s14, gas - 1)
  }

  /** Node 477
    * Segment Id for this node is: 220
    * Starting at 0x11c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[2] == 0x1371

    requires s0.stack[6] == 0x8ac

    requires s0.stack[13] == 0x93e

    requires s0.stack[18] == 0x3d2

    requires s0.stack[24] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1371;
      assert s1.Peek(6) == 0x8ac;
      assert s1.Peek(13) == 0x93e;
      assert s1.Peek(18) == 0x3d2;
      assert s1.Peek(24) == 0x175;
      var s2 := Push2(s1, 0x11cf);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s478(s5, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0x11cf

    requires s0.stack[4] == 0x1371

    requires s0.stack[8] == 0x8ac

    requires s0.stack[15] == 0x93e

    requires s0.stack[20] == 0x3d2

    requires s0.stack[26] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11cf;
      assert s1.Peek(4) == 0x1371;
      assert s1.Peek(8) == 0x8ac;
      assert s1.Peek(15) == 0x93e;
      assert s1.Peek(20) == 0x3d2;
      assert s1.Peek(26) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s479(s9, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 221
    * Starting at 0x11cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0x1371

    requires s0.stack[7] == 0x8ac

    requires s0.stack[14] == 0x93e

    requires s0.stack[19] == 0x3d2

    requires s0.stack[25] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1371;
      assert s1.Peek(7) == 0x8ac;
      assert s1.Peek(14) == 0x93e;
      assert s1.Peek(19) == 0x3d2;
      assert s1.Peek(25) == 0x175;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s480(s6, gas - 1)
  }

  /** Node 480
    * Segment Id for this node is: 249
    * Starting at 0x1371
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x8ac

    requires s0.stack[10] == 0x93e

    requires s0.stack[15] == 0x3d2

    requires s0.stack[21] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8ac;
      assert s1.Peek(10) == 0x93e;
      assert s1.Peek(15) == 0x3d2;
      assert s1.Peek(21) == 0x175;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s481(s6, gas - 1)
  }

  /** Node 481
    * Segment Id for this node is: 136
    * Starting at 0x8ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x93e

    requires s0.stack[12] == 0x3d2

    requires s0.stack[18] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x93e;
      assert s1.Peek(12) == 0x3d2;
      assert s1.Peek(18) == 0x175;
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
      assert s11.Peek(0) == 0x93e;
      assert s11.Peek(5) == 0x3d2;
      assert s11.Peek(11) == 0x175;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s12, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 143
    * Starting at 0x93e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3d2

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s483(s1, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 144
    * Starting at 0x93f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3d2

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3d2;
      assert s1.Peek(10) == 0x175;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s484(s6, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 87
    * Starting at 0x3d2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x175;
      var s2 := Push2(s1, 0x03dd);
      var s3 := Dup6(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Push2(s5, 0x0945);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s7, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 145
    * Starting at 0x945
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x945 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3dd

    requires s0.stack[9] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3dd;
      assert s1.Peek(9) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x09b5);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s493(s11, gas - 1)
      else
        ExecuteFromCFGNode_s486(s11, gas - 1)
  }

  /** Node 486
    * Segment Id for this node is: 146
    * Starting at 0x97b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3dd

    requires s0.stack[9] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3dd;
      assert s1.Peek(10) == 0x175;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x09ac);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12fc);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s487(s11, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 242
    * Starting at 0x12fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x9ac

    requires s0.stack[5] == 0x3dd

    requires s0.stack[11] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9ac;
      assert s1.Peek(5) == 0x3dd;
      assert s1.Peek(11) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x9ac;
      assert s11.Peek(8) == 0x3dd;
      assert s11.Peek(14) == 0x175;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1315);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1094);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s488(s18, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 214
    * Starting at 0x1094
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1315

    requires s0.stack[4] == 0x9ac

    requires s0.stack[8] == 0x3dd

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1315;
      assert s1.Peek(4) == 0x9ac;
      assert s1.Peek(8) == 0x3dd;
      assert s1.Peek(14) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x10a1);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s489(s7, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x10a1

    requires s0.stack[5] == 0x1315

    requires s0.stack[8] == 0x9ac

    requires s0.stack[12] == 0x3dd

    requires s0.stack[18] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10a1;
      assert s1.Peek(5) == 0x1315;
      assert s1.Peek(8) == 0x9ac;
      assert s1.Peek(12) == 0x3dd;
      assert s1.Peek(18) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x10a1;
      assert s11.Peek(6) == 0x1315;
      assert s11.Peek(9) == 0x9ac;
      assert s11.Peek(13) == 0x3dd;
      assert s11.Peek(19) == 0x175;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s490(s15, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 215
    * Starting at 0x10a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1315

    requires s0.stack[6] == 0x9ac

    requires s0.stack[10] == 0x3dd

    requires s0.stack[16] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1315;
      assert s1.Peek(6) == 0x9ac;
      assert s1.Peek(10) == 0x3dd;
      assert s1.Peek(16) == 0x175;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x6472657373000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1315;
      assert s11.Peek(8) == 0x9ac;
      assert s11.Peek(12) == 0x3dd;
      assert s11.Peek(18) == 0x175;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1315;
      assert s21.Peek(4) == 0x9ac;
      assert s21.Peek(8) == 0x3dd;
      assert s21.Peek(14) == 0x175;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s22, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 243
    * Starting at 0x1315
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1315 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x9ac

    requires s0.stack[7] == 0x3dd

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9ac;
      assert s1.Peek(7) == 0x3dd;
      assert s1.Peek(13) == 0x175;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s492(s7, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 147
    * Starting at 0x9ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3dd

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3dd;
      assert s1.Peek(10) == 0x175;
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

  /** Node 493
    * Segment Id for this node is: 148
    * Starting at 0x9b5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3dd

    requires s0.stack[9] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3dd;
      assert s1.Peek(9) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0a25);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s501(s11, gas - 1)
      else
        ExecuteFromCFGNode_s494(s11, gas - 1)
  }

  /** Node 494
    * Segment Id for this node is: 149
    * Starting at 0x9eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3dd

    requires s0.stack[9] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3dd;
      assert s1.Peek(10) == 0x175;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a1c);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x123c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s495(s11, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 230
    * Starting at 0x123c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xa1c

    requires s0.stack[5] == 0x3dd

    requires s0.stack[11] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa1c;
      assert s1.Peek(5) == 0x3dd;
      assert s1.Peek(11) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0xa1c;
      assert s11.Peek(8) == 0x3dd;
      assert s11.Peek(14) == 0x175;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1255);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0e7c);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s496(s18, gas - 1)
  }

  /** Node 496
    * Segment Id for this node is: 202
    * Starting at 0xe7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1255

    requires s0.stack[4] == 0xa1c

    requires s0.stack[8] == 0x3dd

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1255;
      assert s1.Peek(4) == 0xa1c;
      assert s1.Peek(8) == 0x3dd;
      assert s1.Peek(14) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0e89);
      var s4 := Push1(s3, 0x23);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s497(s7, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xe89

    requires s0.stack[5] == 0x1255

    requires s0.stack[8] == 0xa1c

    requires s0.stack[12] == 0x3dd

    requires s0.stack[18] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe89;
      assert s1.Peek(5) == 0x1255;
      assert s1.Peek(8) == 0xa1c;
      assert s1.Peek(12) == 0x3dd;
      assert s1.Peek(18) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xe89;
      assert s11.Peek(6) == 0x1255;
      assert s11.Peek(9) == 0xa1c;
      assert s11.Peek(13) == 0x3dd;
      assert s11.Peek(19) == 0x175;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s15, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 203
    * Starting at 0xe89
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1255

    requires s0.stack[6] == 0xa1c

    requires s0.stack[10] == 0x3dd

    requires s0.stack[16] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1255;
      assert s1.Peek(6) == 0xa1c;
      assert s1.Peek(10) == 0x3dd;
      assert s1.Peek(16) == 0x175;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x6573730000000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1255;
      assert s11.Peek(8) == 0xa1c;
      assert s11.Peek(12) == 0x3dd;
      assert s11.Peek(18) == 0x175;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1255;
      assert s21.Peek(4) == 0xa1c;
      assert s21.Peek(8) == 0x3dd;
      assert s21.Peek(14) == 0x175;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s22, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 231
    * Starting at 0x1255
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1255 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa1c

    requires s0.stack[7] == 0x3dd

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa1c;
      assert s1.Peek(7) == 0x3dd;
      assert s1.Peek(13) == 0x175;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s7, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 150
    * Starting at 0xa1c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3dd

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3dd;
      assert s1.Peek(10) == 0x175;
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

  /** Node 501
    * Segment Id for this node is: 151
    * Starting at 0xa25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3dd

    requires s0.stack[9] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3dd;
      assert s1.Peek(9) == 0x175;
      var s2 := Push2(s1, 0x0a30);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d01);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s502(s7, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 167
    * Starting at 0xd01
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd01 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa30

    requires s0.stack[7] == 0x3dd

    requires s0.stack[13] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa30;
      assert s1.Peek(7) == 0x3dd;
      assert s1.Peek(13) == 0x175;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s503(s5, gas - 1)
  }

  /** Node 503
    * Segment Id for this node is: 152
    * Starting at 0xa30
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3dd

    requires s0.stack[9] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3dd;
      assert s1.Peek(9) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x3dd;
      assert s11.Peek(12) == 0x175;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x3dd;
      assert s21.Peek(11) == 0x175;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0ab6);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s511(s29, gas - 1)
      else
        ExecuteFromCFGNode_s504(s29, gas - 1)
  }

  /** Node 504
    * Segment Id for this node is: 153
    * Starting at 0xa7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3dd

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x3dd;
      assert s1.Peek(11) == 0x175;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0aad);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12bc);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s505(s11, gas - 1)
  }

  /** Node 505
    * Segment Id for this node is: 238
    * Starting at 0x12bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xaad

    requires s0.stack[6] == 0x3dd

    requires s0.stack[12] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaad;
      assert s1.Peek(6) == 0x3dd;
      assert s1.Peek(12) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0xaad;
      assert s11.Peek(9) == 0x3dd;
      assert s11.Peek(15) == 0x175;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12d5);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0fee);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s506(s18, gas - 1)
  }

  /** Node 506
    * Segment Id for this node is: 210
    * Starting at 0xfee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x12d5

    requires s0.stack[4] == 0xaad

    requires s0.stack[9] == 0x3dd

    requires s0.stack[15] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12d5;
      assert s1.Peek(4) == 0xaad;
      assert s1.Peek(9) == 0x3dd;
      assert s1.Peek(15) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ffb);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s507(s7, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xffb

    requires s0.stack[5] == 0x12d5

    requires s0.stack[8] == 0xaad

    requires s0.stack[13] == 0x3dd

    requires s0.stack[19] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xffb;
      assert s1.Peek(5) == 0x12d5;
      assert s1.Peek(8) == 0xaad;
      assert s1.Peek(13) == 0x3dd;
      assert s1.Peek(19) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xffb;
      assert s11.Peek(6) == 0x12d5;
      assert s11.Peek(9) == 0xaad;
      assert s11.Peek(14) == 0x3dd;
      assert s11.Peek(20) == 0x175;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s508(s15, gas - 1)
  }

  /** Node 508
    * Segment Id for this node is: 211
    * Starting at 0xffb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x12d5

    requires s0.stack[6] == 0xaad

    requires s0.stack[11] == 0x3dd

    requires s0.stack[17] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12d5;
      assert s1.Peek(6) == 0xaad;
      assert s1.Peek(11) == 0x3dd;
      assert s1.Peek(17) == 0x175;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x616c616e63650000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x12d5;
      assert s11.Peek(8) == 0xaad;
      assert s11.Peek(13) == 0x3dd;
      assert s11.Peek(19) == 0x175;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x12d5;
      assert s21.Peek(4) == 0xaad;
      assert s21.Peek(9) == 0x3dd;
      assert s21.Peek(15) == 0x175;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s509(s22, gas - 1)
  }

  /** Node 509
    * Segment Id for this node is: 239
    * Starting at 0x12d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xaad

    requires s0.stack[8] == 0x3dd

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaad;
      assert s1.Peek(8) == 0x3dd;
      assert s1.Peek(14) == 0x175;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s510(s7, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 154
    * Starting at 0xaad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x3dd

    requires s0.stack[11] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3dd;
      assert s1.Peek(11) == 0x175;
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

  /** Node 511
    * Segment Id for this node is: 155
    * Starting at 0xab6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3dd

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3dd;
      assert s1.Peek(10) == 0x175;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup1(s5);
      var s7 := Dup7(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x3dd;
      assert s11.Peek(14) == 0x175;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(7) == 0x3dd;
      assert s21.Peek(13) == 0x175;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Dup2(s26);
      var s28 := Push1(s27, 0x00);
      var s29 := Dup1(s28);
      var s30 := Dup6(s29);
      var s31 := Push20(s30, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s31.Peek(9) == 0x3dd;
      assert s31.Peek(15) == 0x175;
      var s32 := And(s31);
      var s33 := Push20(s32, 0xffffffffffffffffffffffffffffffffffffffff);
      var s34 := And(s33);
      var s35 := Dup2(s34);
      var s36 := MStore(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Add(s37);
      var s39 := Swap1(s38);
      var s40 := Dup2(s39);
      var s41 := MStore(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s512(s41, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 156
    * Starting at 0xb35
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x3dd

    requires s0.stack[12] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x3dd;
      assert s1.Peek(13) == 0x175;
      var s2 := Add(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Keccak256(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup3(s5);
      var s7 := Dup3(s6);
      var s8 := SLoad(s7);
      var s9 := Add(s8);
      var s10 := Swap3(s9);
      var s11 := Pop(s10);
      assert s11.Peek(7) == 0x3dd;
      assert s11.Peek(13) == 0x175;
      var s12 := Pop(s11);
      var s13 := Dup2(s12);
      var s14 := Swap1(s13);
      var s15 := SStore(s14);
      var s16 := Pop(s15);
      var s17 := Dup3(s16);
      var s18 := Push20(s17, 0xffffffffffffffffffffffffffffffffffffffff);
      var s19 := And(s18);
      var s20 := Dup5(s19);
      var s21 := Push20(s20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s21.Peek(7) == 0x3dd;
      assert s21.Peek(13) == 0x175;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup5(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x0ba4);
      var s28 := Swap2(s27);
      var s29 := Swap1(s28);
      var s30 := Push2(s29, 0x135c);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s31, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 248
    * Starting at 0x135c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xba4

    requires s0.stack[10] == 0x3dd

    requires s0.stack[16] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xba4;
      assert s1.Peek(10) == 0x3dd;
      assert s1.Peek(16) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1371);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1371;
      assert s11.Peek(5) == 0xba4;
      assert s11.Peek(13) == 0x3dd;
      assert s11.Peek(19) == 0x175;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x11c6);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s514(s14, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 220
    * Starting at 0x11c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x1371

    requires s0.stack[6] == 0xba4

    requires s0.stack[14] == 0x3dd

    requires s0.stack[20] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1371;
      assert s1.Peek(6) == 0xba4;
      assert s1.Peek(14) == 0x3dd;
      assert s1.Peek(20) == 0x175;
      var s2 := Push2(s1, 0x11cf);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s515(s5, gas - 1)
  }

  /** Node 515
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x11cf

    requires s0.stack[4] == 0x1371

    requires s0.stack[8] == 0xba4

    requires s0.stack[16] == 0x3dd

    requires s0.stack[22] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11cf;
      assert s1.Peek(4) == 0x1371;
      assert s1.Peek(8) == 0xba4;
      assert s1.Peek(16) == 0x3dd;
      assert s1.Peek(22) == 0x175;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s516(s9, gas - 1)
  }

  /** Node 516
    * Segment Id for this node is: 221
    * Starting at 0x11cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x1371

    requires s0.stack[7] == 0xba4

    requires s0.stack[15] == 0x3dd

    requires s0.stack[21] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1371;
      assert s1.Peek(7) == 0xba4;
      assert s1.Peek(15) == 0x3dd;
      assert s1.Peek(21) == 0x175;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s517(s6, gas - 1)
  }

  /** Node 517
    * Segment Id for this node is: 249
    * Starting at 0x1371
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xba4

    requires s0.stack[11] == 0x3dd

    requires s0.stack[17] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xba4;
      assert s1.Peek(11) == 0x3dd;
      assert s1.Peek(17) == 0x175;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s518(s6, gas - 1)
  }

  /** Node 518
    * Segment Id for this node is: 157
    * Starting at 0xba4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x3dd

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3dd;
      assert s1.Peek(14) == 0x175;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push2(s8, 0x0bb7);
      var s10 := Dup5(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(2) == 0xbb7;
      assert s11.Peek(7) == 0x3dd;
      assert s11.Peek(13) == 0x175;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d06);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s519(s14, gas - 1)
  }

  /** Node 519
    * Segment Id for this node is: 168
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xbb7

    requires s0.stack[8] == 0x3dd

    requires s0.stack[14] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbb7;
      assert s1.Peek(8) == 0x3dd;
      assert s1.Peek(14) == 0x175;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s520(s5, gas - 1)
  }

  /** Node 520
    * Segment Id for this node is: 158
    * Starting at 0xbb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3dd

    requires s0.stack[10] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3dd;
      assert s1.Peek(10) == 0x175;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s521(s6, gas - 1)
  }

  /** Node 521
    * Segment Id for this node is: 88
    * Starting at 0x3dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x175

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x175;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap4(s5);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s522(s11, gas - 1)
  }

  /** Node 522
    * Segment Id for this node is: 36
    * Starting at 0x175
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x175 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0182);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11ff);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s523(s8, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 226
    * Starting at 0x11ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x182

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x182;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1214);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1214;
      assert s11.Peek(5) == 0x182;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e34);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s524(s14, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 195
    * Starting at 0xe34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1214

    requires s0.stack[6] == 0x182

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1214;
      assert s1.Peek(6) == 0x182;
      var s2 := Push2(s1, 0x0e3d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1416);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s525(s5, gas - 1)
  }

  /** Node 525
    * Segment Id for this node is: 262
    * Starting at 0x1416
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1416 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe3d

    requires s0.stack[4] == 0x1214

    requires s0.stack[8] == 0x182

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe3d;
      assert s1.Peek(4) == 0x1214;
      assert s1.Peek(8) == 0x182;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s526(s11, gas - 1)
  }

  /** Node 526
    * Segment Id for this node is: 196
    * Starting at 0xe3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1214

    requires s0.stack[7] == 0x182

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1214;
      assert s1.Peek(7) == 0x182;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s527(s6, gas - 1)
  }

  /** Node 527
    * Segment Id for this node is: 227
    * Starting at 0x1214
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1214 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x182

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x182;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s528(s6, gas - 1)
  }

  /** Node 528
    * Segment Id for this node is: 37
    * Starting at 0x182
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x182 as nat
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

  /** Node 529
    * Segment Id for this node is: 20
    * Starting at 0xc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x06fdde03);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00ef);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s599(s6, gas - 1)
      else
        ExecuteFromCFGNode_s530(s6, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 21
    * Starting at 0xd4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x010d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s541(s5, gas - 1)
      else
        ExecuteFromCFGNode_s531(s5, gas - 1)
  }

  /** Node 531
    * Segment Id for this node is: 22
    * Starting at 0xdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x013d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s532(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 532
    * Segment Id for this node is: 31
    * Starting at 0x13d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0145);
      var s3 := Push2(s2, 0x03b0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s533(s4, gas - 1)
  }

  /** Node 533
    * Segment Id for this node is: 84
    * Starting at 0x3b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x145

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x145;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s534(s8, gas - 1)
  }

  /** Node 534
    * Segment Id for this node is: 32
    * Starting at 0x145
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0152);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x135c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s535(s8, gas - 1)
  }

  /** Node 535
    * Segment Id for this node is: 248
    * Starting at 0x135c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x152

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x152;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1371);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1371;
      assert s11.Peek(5) == 0x152;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x11c6);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s536(s14, gas - 1)
  }

  /** Node 536
    * Segment Id for this node is: 220
    * Starting at 0x11c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1371

    requires s0.stack[6] == 0x152

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1371;
      assert s1.Peek(6) == 0x152;
      var s2 := Push2(s1, 0x11cf);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s537(s5, gas - 1)
  }

  /** Node 537
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x11cf

    requires s0.stack[4] == 0x1371

    requires s0.stack[8] == 0x152

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11cf;
      assert s1.Peek(4) == 0x1371;
      assert s1.Peek(8) == 0x152;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s538(s9, gas - 1)
  }

  /** Node 538
    * Segment Id for this node is: 221
    * Starting at 0x11cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1371

    requires s0.stack[7] == 0x152

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1371;
      assert s1.Peek(7) == 0x152;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s539(s6, gas - 1)
  }

  /** Node 539
    * Segment Id for this node is: 249
    * Starting at 0x1371
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x152

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x152;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s540(s6, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
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

  /** Node 541
    * Segment Id for this node is: 27
    * Starting at 0x10d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0127);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0122);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x122;
      assert s11.Peek(3) == 0x127;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0de9);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s14, gas - 1)
  }

  /** Node 542
    * Segment Id for this node is: 188
    * Starting at 0xde9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x122

    requires s0.stack[3] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x122;
      assert s1.Peek(3) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0dfc);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s544(s11, gas - 1)
      else
        ExecuteFromCFGNode_s543(s11, gas - 1)
  }

  /** Node 543
    * Segment Id for this node is: 189
    * Starting at 0xdf8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x122

    requires s0.stack[5] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x122;
      assert s1.Peek(6) == 0x127;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 544
    * Segment Id for this node is: 190
    * Starting at 0xdfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x122

    requires s0.stack[5] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x122;
      assert s1.Peek(5) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0e0a);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d0b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s545(s9, gas - 1)
  }

  /** Node 545
    * Segment Id for this node is: 169
    * Starting at 0xd0b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe0a

    requires s0.stack[8] == 0x122

    requires s0.stack[9] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe0a;
      assert s1.Peek(8) == 0x122;
      assert s1.Peek(9) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d1a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x152d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s546(s10, gas - 1)
  }

  /** Node 546
    * Segment Id for this node is: 281
    * Starting at 0x152d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x122

    requires s0.stack[12] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xe0a;
      assert s1.Peek(11) == 0x122;
      assert s1.Peek(12) == 0x127;
      var s2 := Push2(s1, 0x1536);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1404);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s547(s5, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 260
    * Starting at 0x1404
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1536

    requires s0.stack[3] == 0xd1a

    requires s0.stack[7] == 0xe0a

    requires s0.stack[13] == 0x122

    requires s0.stack[14] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1536;
      assert s1.Peek(3) == 0xd1a;
      assert s1.Peek(7) == 0xe0a;
      assert s1.Peek(13) == 0x122;
      assert s1.Peek(14) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x140f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1422);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s548(s6, gas - 1)
  }

  /** Node 548
    * Segment Id for this node is: 263
    * Starting at 0x1422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x140f

    requires s0.stack[4] == 0x1536

    requires s0.stack[6] == 0xd1a

    requires s0.stack[10] == 0xe0a

    requires s0.stack[16] == 0x122

    requires s0.stack[17] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x140f;
      assert s1.Peek(4) == 0x1536;
      assert s1.Peek(6) == 0xd1a;
      assert s1.Peek(10) == 0xe0a;
      assert s1.Peek(16) == 0x122;
      assert s1.Peek(17) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s549(s11, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 261
    * Starting at 0x140f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1536

    requires s0.stack[5] == 0xd1a

    requires s0.stack[9] == 0xe0a

    requires s0.stack[15] == 0x122

    requires s0.stack[16] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1536;
      assert s1.Peek(5) == 0xd1a;
      assert s1.Peek(9) == 0xe0a;
      assert s1.Peek(15) == 0x122;
      assert s1.Peek(16) == 0x127;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s550(s7, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 282
    * Starting at 0x1536
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd1a

    requires s0.stack[6] == 0xe0a

    requires s0.stack[12] == 0x122

    requires s0.stack[13] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xe0a;
      assert s1.Peek(12) == 0x122;
      assert s1.Peek(13) == 0x127;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1541);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s552(s5, gas - 1)
      else
        ExecuteFromCFGNode_s551(s5, gas - 1)
  }

  /** Node 551
    * Segment Id for this node is: 283
    * Starting at 0x153d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x122

    requires s0.stack[12] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd1a;
      assert s1.Peek(6) == 0xe0a;
      assert s1.Peek(12) == 0x122;
      assert s1.Peek(13) == 0x127;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 552
    * Segment Id for this node is: 284
    * Starting at 0x1541
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd1a

    requires s0.stack[5] == 0xe0a

    requires s0.stack[11] == 0x122

    requires s0.stack[12] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd1a;
      assert s1.Peek(5) == 0xe0a;
      assert s1.Peek(11) == 0x122;
      assert s1.Peek(12) == 0x127;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s553(s3, gas - 1)
  }

  /** Node 553
    * Segment Id for this node is: 170
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe0a

    requires s0.stack[9] == 0x122

    requires s0.stack[10] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe0a;
      assert s1.Peek(9) == 0x122;
      assert s1.Peek(10) == 0x127;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s554(s6, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 191
    * Starting at 0xe0a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x122

    requires s0.stack[7] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x122;
      assert s1.Peek(7) == 0x127;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0e1b);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d20);
      assert s11.Peek(0) == 0xd20;
      assert s11.Peek(3) == 0xe1b;
      assert s11.Peek(9) == 0x122;
      assert s11.Peek(10) == 0x127;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s555(s12, gas - 1)
  }

  /** Node 555
    * Segment Id for this node is: 171
    * Starting at 0xd20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe1b

    requires s0.stack[8] == 0x122

    requires s0.stack[9] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe1b;
      assert s1.Peek(8) == 0x122;
      assert s1.Peek(9) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d2f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x1544);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s556(s10, gas - 1)
  }

  /** Node 556
    * Segment Id for this node is: 285
    * Starting at 0x1544
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1544 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x122

    requires s0.stack[12] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(5) == 0xe1b;
      assert s1.Peek(11) == 0x122;
      assert s1.Peek(12) == 0x127;
      var s2 := Push2(s1, 0x154d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s557(s5, gas - 1)
  }

  /** Node 557
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s557(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x154d

    requires s0.stack[3] == 0xd2f

    requires s0.stack[7] == 0xe1b

    requires s0.stack[13] == 0x122

    requires s0.stack[14] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x154d;
      assert s1.Peek(3) == 0xd2f;
      assert s1.Peek(7) == 0xe1b;
      assert s1.Peek(13) == 0x122;
      assert s1.Peek(14) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s558(s9, gas - 1)
  }

  /** Node 558
    * Segment Id for this node is: 286
    * Starting at 0x154d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s558(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd2f

    requires s0.stack[6] == 0xe1b

    requires s0.stack[12] == 0x122

    requires s0.stack[13] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd2f;
      assert s1.Peek(6) == 0xe1b;
      assert s1.Peek(12) == 0x122;
      assert s1.Peek(13) == 0x127;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1558);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s560(s5, gas - 1)
      else
        ExecuteFromCFGNode_s559(s5, gas - 1)
  }

  /** Node 559
    * Segment Id for this node is: 287
    * Starting at 0x1554
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s559(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1554 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x122

    requires s0.stack[12] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd2f;
      assert s1.Peek(6) == 0xe1b;
      assert s1.Peek(12) == 0x122;
      assert s1.Peek(13) == 0x127;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 560
    * Segment Id for this node is: 288
    * Starting at 0x1558
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s560(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1558 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2f

    requires s0.stack[5] == 0xe1b

    requires s0.stack[11] == 0x122

    requires s0.stack[12] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(5) == 0xe1b;
      assert s1.Peek(11) == 0x122;
      assert s1.Peek(12) == 0x127;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s561(s3, gas - 1)
  }

  /** Node 561
    * Segment Id for this node is: 172
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s561(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe1b

    requires s0.stack[9] == 0x122

    requires s0.stack[10] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe1b;
      assert s1.Peek(9) == 0x122;
      assert s1.Peek(10) == 0x127;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s562(s6, gas - 1)
  }

  /** Node 562
    * Segment Id for this node is: 192
    * Starting at 0xe1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s562(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x122

    requires s0.stack[7] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x122;
      assert s1.Peek(7) == 0x127;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s563(s10, gas - 1)
  }

  /** Node 563
    * Segment Id for this node is: 28
    * Starting at 0x122
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s563(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x127;
      var s2 := Push2(s1, 0x038d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s564(s3, gas - 1)
  }

  /** Node 564
    * Segment Id for this node is: 81
    * Starting at 0x38d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s564(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0398);
      var s5 := Push2(s4, 0x06e6);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s565(s6, gas - 1)
  }

  /** Node 565
    * Segment Id for this node is: 127
    * Starting at 0x6e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s565(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x398

    requires s0.stack[5] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x398;
      assert s1.Peek(5) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s566(s7, gas - 1)
  }

  /** Node 566
    * Segment Id for this node is: 82
    * Starting at 0x398
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s566(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x398 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x127;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x03a5);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x06ee);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s567(s9, gas - 1)
  }

  /** Node 567
    * Segment Id for this node is: 128
    * Starting at 0x6ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s567(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3a5

    requires s0.stack[8] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3a5;
      assert s1.Peek(8) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x075e);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s575(s11, gas - 1)
      else
        ExecuteFromCFGNode_s568(s11, gas - 1)
  }

  /** Node 568
    * Segment Id for this node is: 129
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s568(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3a5

    requires s0.stack[8] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3a5;
      assert s1.Peek(9) == 0x127;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0755);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x131c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s569(s11, gas - 1)
  }

  /** Node 569
    * Segment Id for this node is: 244
    * Starting at 0x131c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s569(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x755

    requires s0.stack[5] == 0x3a5

    requires s0.stack[10] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x755;
      assert s1.Peek(5) == 0x3a5;
      assert s1.Peek(10) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x755;
      assert s11.Peek(8) == 0x3a5;
      assert s11.Peek(13) == 0x127;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1335);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10fa);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s570(s18, gas - 1)
  }

  /** Node 570
    * Segment Id for this node is: 216
    * Starting at 0x10fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s570(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1335

    requires s0.stack[4] == 0x755

    requires s0.stack[8] == 0x3a5

    requires s0.stack[13] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1335;
      assert s1.Peek(4) == 0x755;
      assert s1.Peek(8) == 0x3a5;
      assert s1.Peek(13) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1107);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s571(s7, gas - 1)
  }

  /** Node 571
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s571(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1107

    requires s0.stack[5] == 0x1335

    requires s0.stack[8] == 0x755

    requires s0.stack[12] == 0x3a5

    requires s0.stack[17] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1107;
      assert s1.Peek(5) == 0x1335;
      assert s1.Peek(8) == 0x755;
      assert s1.Peek(12) == 0x3a5;
      assert s1.Peek(17) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1107;
      assert s11.Peek(6) == 0x1335;
      assert s11.Peek(9) == 0x755;
      assert s11.Peek(13) == 0x3a5;
      assert s11.Peek(18) == 0x127;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s572(s15, gas - 1)
  }

  /** Node 572
    * Segment Id for this node is: 217
    * Starting at 0x1107
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s572(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1107 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1335

    requires s0.stack[6] == 0x755

    requires s0.stack[10] == 0x3a5

    requires s0.stack[15] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1335;
      assert s1.Peek(6) == 0x755;
      assert s1.Peek(10) == 0x3a5;
      assert s1.Peek(15) == 0x127;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1335;
      assert s11.Peek(8) == 0x755;
      assert s11.Peek(12) == 0x3a5;
      assert s11.Peek(17) == 0x127;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1335;
      assert s21.Peek(4) == 0x755;
      assert s21.Peek(8) == 0x3a5;
      assert s21.Peek(13) == 0x127;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s573(s22, gas - 1)
  }

  /** Node 573
    * Segment Id for this node is: 245
    * Starting at 0x1335
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s573(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1335 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x755

    requires s0.stack[7] == 0x3a5

    requires s0.stack[12] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x755;
      assert s1.Peek(7) == 0x3a5;
      assert s1.Peek(12) == 0x127;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s574(s7, gas - 1)
  }

  /** Node 574
    * Segment Id for this node is: 130
    * Starting at 0x755
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s574(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x755 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x3a5

    requires s0.stack[9] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3a5;
      assert s1.Peek(9) == 0x127;
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

  /** Node 575
    * Segment Id for this node is: 131
    * Starting at 0x75e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s575(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3a5

    requires s0.stack[8] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3a5;
      assert s1.Peek(8) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x07ce);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s583(s11, gas - 1)
      else
        ExecuteFromCFGNode_s576(s11, gas - 1)
  }

  /** Node 576
    * Segment Id for this node is: 132
    * Starting at 0x794
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s576(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x794 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3a5

    requires s0.stack[8] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3a5;
      assert s1.Peek(9) == 0x127;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x07c5);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x127c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s577(s11, gas - 1)
  }

  /** Node 577
    * Segment Id for this node is: 234
    * Starting at 0x127c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s577(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x7c5

    requires s0.stack[5] == 0x3a5

    requires s0.stack[10] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7c5;
      assert s1.Peek(5) == 0x3a5;
      assert s1.Peek(10) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x7c5;
      assert s11.Peek(8) == 0x3a5;
      assert s11.Peek(13) == 0x127;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1295);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0f48);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s578(s18, gas - 1)
  }

  /** Node 578
    * Segment Id for this node is: 206
    * Starting at 0xf48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s578(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1295

    requires s0.stack[4] == 0x7c5

    requires s0.stack[8] == 0x3a5

    requires s0.stack[13] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1295;
      assert s1.Peek(4) == 0x7c5;
      assert s1.Peek(8) == 0x3a5;
      assert s1.Peek(13) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0f55);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x139d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s579(s7, gas - 1)
  }

  /** Node 579
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s579(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xf55

    requires s0.stack[5] == 0x1295

    requires s0.stack[8] == 0x7c5

    requires s0.stack[12] == 0x3a5

    requires s0.stack[17] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf55;
      assert s1.Peek(5) == 0x1295;
      assert s1.Peek(8) == 0x7c5;
      assert s1.Peek(12) == 0x3a5;
      assert s1.Peek(17) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xf55;
      assert s11.Peek(6) == 0x1295;
      assert s11.Peek(9) == 0x7c5;
      assert s11.Peek(13) == 0x3a5;
      assert s11.Peek(18) == 0x127;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s580(s15, gas - 1)
  }

  /** Node 580
    * Segment Id for this node is: 207
    * Starting at 0xf55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s580(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1295

    requires s0.stack[6] == 0x7c5

    requires s0.stack[10] == 0x3a5

    requires s0.stack[15] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1295;
      assert s1.Peek(6) == 0x7c5;
      assert s1.Peek(10) == 0x3a5;
      assert s1.Peek(15) == 0x127;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x1295;
      assert s11.Peek(8) == 0x7c5;
      assert s11.Peek(12) == 0x3a5;
      assert s11.Peek(17) == 0x127;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x1295;
      assert s21.Peek(4) == 0x7c5;
      assert s21.Peek(8) == 0x3a5;
      assert s21.Peek(13) == 0x127;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s581(s22, gas - 1)
  }

  /** Node 581
    * Segment Id for this node is: 235
    * Starting at 0x1295
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s581(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x7c5

    requires s0.stack[7] == 0x3a5

    requires s0.stack[12] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7c5;
      assert s1.Peek(7) == 0x3a5;
      assert s1.Peek(12) == 0x127;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s582(s7, gas - 1)
  }

  /** Node 582
    * Segment Id for this node is: 133
    * Starting at 0x7c5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s582(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x3a5

    requires s0.stack[9] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3a5;
      assert s1.Peek(9) == 0x127;
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

  /** Node 583
    * Segment Id for this node is: 134
    * Starting at 0x7ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s583(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3a5

    requires s0.stack[8] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3a5;
      assert s1.Peek(8) == 0x127;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x3a5;
      assert s11.Peek(11) == 0x127;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(6) == 0x3a5;
      assert s21.Peek(11) == 0x127;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x3a5;
      assert s31.Peek(11) == 0x127;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x00);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s584(s41, gas - 1)
  }

  /** Node 584
    * Segment Id for this node is: 135
    * Starting at 0x850
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s584(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x850 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3a5

    requires s0.stack[8] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x3a5;
      assert s1.Peek(9) == 0x127;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08ac);
      assert s11.Peek(0) == 0x8ac;
      assert s11.Peek(9) == 0x3a5;
      assert s11.Peek(14) == 0x127;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x135c);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s585(s15, gas - 1)
  }

  /** Node 585
    * Segment Id for this node is: 248
    * Starting at 0x135c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s585(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x8ac

    requires s0.stack[9] == 0x3a5

    requires s0.stack[14] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8ac;
      assert s1.Peek(9) == 0x3a5;
      assert s1.Peek(14) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1371);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1371;
      assert s11.Peek(5) == 0x8ac;
      assert s11.Peek(12) == 0x3a5;
      assert s11.Peek(17) == 0x127;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x11c6);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s586(s14, gas - 1)
  }

  /** Node 586
    * Segment Id for this node is: 220
    * Starting at 0x11c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s586(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x1371

    requires s0.stack[6] == 0x8ac

    requires s0.stack[13] == 0x3a5

    requires s0.stack[18] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1371;
      assert s1.Peek(6) == 0x8ac;
      assert s1.Peek(13) == 0x3a5;
      assert s1.Peek(18) == 0x127;
      var s2 := Push2(s1, 0x11cf);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1442);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s587(s5, gas - 1)
  }

  /** Node 587
    * Segment Id for this node is: 264
    * Starting at 0x1442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s587(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x11cf

    requires s0.stack[4] == 0x1371

    requires s0.stack[8] == 0x8ac

    requires s0.stack[15] == 0x3a5

    requires s0.stack[20] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11cf;
      assert s1.Peek(4) == 0x1371;
      assert s1.Peek(8) == 0x8ac;
      assert s1.Peek(15) == 0x3a5;
      assert s1.Peek(20) == 0x127;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s588(s9, gas - 1)
  }

  /** Node 588
    * Segment Id for this node is: 221
    * Starting at 0x11cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s588(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x1371

    requires s0.stack[7] == 0x8ac

    requires s0.stack[14] == 0x3a5

    requires s0.stack[19] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1371;
      assert s1.Peek(7) == 0x8ac;
      assert s1.Peek(14) == 0x3a5;
      assert s1.Peek(19) == 0x127;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s589(s6, gas - 1)
  }

  /** Node 589
    * Segment Id for this node is: 249
    * Starting at 0x1371
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s589(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x8ac

    requires s0.stack[10] == 0x3a5

    requires s0.stack[15] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8ac;
      assert s1.Peek(10) == 0x3a5;
      assert s1.Peek(15) == 0x127;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s590(s6, gas - 1)
  }

  /** Node 590
    * Segment Id for this node is: 136
    * Starting at 0x8ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s590(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x3a5

    requires s0.stack[12] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3a5;
      assert s1.Peek(12) == 0x127;
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
      assert s11.Peek(0) == 0x3a5;
      assert s11.Peek(5) == 0x127;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s591(s12, gas - 1)
  }

  /** Node 591
    * Segment Id for this node is: 83
    * Starting at 0x3a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s591(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x127

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x127;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s592(s10, gas - 1)
  }

  /** Node 592
    * Segment Id for this node is: 29
    * Starting at 0x127
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s592(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0134);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x11ff);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s593(s8, gas - 1)
  }

  /** Node 593
    * Segment Id for this node is: 226
    * Starting at 0x11ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s593(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x134;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1214);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1214;
      assert s11.Peek(5) == 0x134;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e34);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s594(s14, gas - 1)
  }

  /** Node 594
    * Segment Id for this node is: 195
    * Starting at 0xe34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s594(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1214

    requires s0.stack[6] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1214;
      assert s1.Peek(6) == 0x134;
      var s2 := Push2(s1, 0x0e3d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1416);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s595(s5, gas - 1)
  }

  /** Node 595
    * Segment Id for this node is: 262
    * Starting at 0x1416
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s595(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1416 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe3d

    requires s0.stack[4] == 0x1214

    requires s0.stack[8] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe3d;
      assert s1.Peek(4) == 0x1214;
      assert s1.Peek(8) == 0x134;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s596(s11, gas - 1)
  }

  /** Node 596
    * Segment Id for this node is: 196
    * Starting at 0xe3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s596(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1214

    requires s0.stack[7] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1214;
      assert s1.Peek(7) == 0x134;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s597(s6, gas - 1)
  }

  /** Node 597
    * Segment Id for this node is: 227
    * Starting at 0x1214
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s597(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1214 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x134

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x134;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s598(s6, gas - 1)
  }

  /** Node 598
    * Segment Id for this node is: 30
    * Starting at 0x134
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s598(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x134 as nat
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

  /** Node 599
    * Segment Id for this node is: 24
    * Starting at 0xef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s599(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00f7);
      var s3 := Push2(s2, 0x02fb);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s600(s4, gas - 1)
  }

  /** Node 600
    * Segment Id for this node is: 72
    * Starting at 0x2fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s600(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf7;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x03);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x030a);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x148c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s601(s9, gas - 1)
  }

  /** Node 601
    * Segment Id for this node is: 272
    * Starting at 0x148c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s601(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x148c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x30a

    requires s0.stack[4] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x30a;
      assert s1.Peek(4) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x30a;
      assert s11.Peek(7) == 0xf7;
      var s12 := Push2(s11, 0x14a4);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s603(s13, gas - 1)
      else
        ExecuteFromCFGNode_s602(s13, gas - 1)
  }

  /** Node 602
    * Segment Id for this node is: 273
    * Starting at 0x149e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s602(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x149e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x30a

    requires s0.stack[6] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x30a;
      assert s1.Peek(7) == 0xf7;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s603(s5, gas - 1)
  }

  /** Node 603
    * Segment Id for this node is: 274
    * Starting at 0x14a4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s603(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x30a

    requires s0.stack[6] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x30a;
      assert s1.Peek(6) == 0xf7;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x14b8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s606(s9, gas - 1)
      else
        ExecuteFromCFGNode_s604(s9, gas - 1)
  }

  /** Node 604
    * Segment Id for this node is: 275
    * Starting at 0x14b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s604(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x30a

    requires s0.stack[6] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x14b7);
      assert s1.Peek(0) == 0x14b7;
      assert s1.Peek(4) == 0x30a;
      assert s1.Peek(7) == 0xf7;
      var s2 := Push2(s1, 0x14ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s605(s3, gas - 1)
  }

  /** Node 605
    * Segment Id for this node is: 279
    * Starting at 0x14ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s605(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x14b7

    requires s0.stack[4] == 0x30a

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x14b7;
      assert s1.Peek(4) == 0x30a;
      assert s1.Peek(7) == 0xf7;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 606
    * Segment Id for this node is: 277
    * Starting at 0x14b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s606(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x30a

    requires s0.stack[6] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x30a;
      assert s1.Peek(6) == 0xf7;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s607(s6, gas - 1)
  }

  /** Node 607
    * Segment Id for this node is: 73
    * Starting at 0x30a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s607(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf7;
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
      assert s11.Peek(4) == 0xf7;
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
      assert s21.Peek(5) == 0xf7;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x0336);
      assert s31.Peek(0) == 0x336;
      assert s31.Peek(8) == 0xf7;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x148c);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s608(s34, gas - 1)
  }

  /** Node 608
    * Segment Id for this node is: 272
    * Starting at 0x148c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s608(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x148c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x336

    requires s0.stack[8] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x336;
      assert s1.Peek(8) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x336;
      assert s11.Peek(11) == 0xf7;
      var s12 := Push2(s11, 0x14a4);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s610(s13, gas - 1)
      else
        ExecuteFromCFGNode_s609(s13, gas - 1)
  }

  /** Node 609
    * Segment Id for this node is: 273
    * Starting at 0x149e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s609(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x149e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x336

    requires s0.stack[10] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x336;
      assert s1.Peek(11) == 0xf7;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s610(s5, gas - 1)
  }

  /** Node 610
    * Segment Id for this node is: 274
    * Starting at 0x14a4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s610(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x336

    requires s0.stack[10] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x336;
      assert s1.Peek(10) == 0xf7;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x14b8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s613(s9, gas - 1)
      else
        ExecuteFromCFGNode_s611(s9, gas - 1)
  }

  /** Node 611
    * Segment Id for this node is: 275
    * Starting at 0x14b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s611(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x336

    requires s0.stack[10] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x14b7);
      assert s1.Peek(0) == 0x14b7;
      assert s1.Peek(4) == 0x336;
      assert s1.Peek(11) == 0xf7;
      var s2 := Push2(s1, 0x14ed);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s612(s3, gas - 1)
  }

  /** Node 612
    * Segment Id for this node is: 279
    * Starting at 0x14ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s612(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x14b7

    requires s0.stack[4] == 0x336

    requires s0.stack[11] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x14b7;
      assert s1.Peek(4) == 0x336;
      assert s1.Peek(11) == 0xf7;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 613
    * Segment Id for this node is: 277
    * Starting at 0x14b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s613(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x336

    requires s0.stack[10] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x336;
      assert s1.Peek(10) == 0xf7;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s614(s6, gas - 1)
  }

  /** Node 614
    * Segment Id for this node is: 74
    * Starting at 0x336
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s614(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x336 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xf7;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0383);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s617(s5, gas - 1)
      else
        ExecuteFromCFGNode_s615(s5, gas - 1)
  }

  /** Node 615
    * Segment Id for this node is: 75
    * Starting at 0x33d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s615(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0xf7;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0358);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s636(s5, gas - 1)
      else
        ExecuteFromCFGNode_s616(s5, gas - 1)
  }

  /** Node 616
    * Segment Id for this node is: 76
    * Starting at 0x345
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s616(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x345 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0xf7;
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
      assert s11.Peek(7) == 0xf7;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0383);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s617(s14, gas - 1)
  }

  /** Node 617
    * Segment Id for this node is: 80
    * Starting at 0x383
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s617(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x383 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xf7;
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
      ExecuteFromCFGNode_s618(s10, gas - 1)
  }

  /** Node 618
    * Segment Id for this node is: 25
    * Starting at 0xf7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s618(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0104);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x121a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s619(s8, gas - 1)
  }

  /** Node 619
    * Segment Id for this node is: 228
    * Starting at 0x121a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s619(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x104;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x104;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1234);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0e43);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s620(s19, gas - 1)
  }

  /** Node 620
    * Segment Id for this node is: 197
    * Starting at 0xe43
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s620(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1234

    requires s0.stack[6] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1234;
      assert s1.Peek(6) == 0x104;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0e4e);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x1392);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s621(s6, gas - 1)
  }

  /** Node 621
    * Segment Id for this node is: 252
    * Starting at 0x1392
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s621(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1392 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xe4e

    requires s0.stack[5] == 0x1234

    requires s0.stack[9] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe4e;
      assert s1.Peek(5) == 0x1234;
      assert s1.Peek(9) == 0x104;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s622(s10, gas - 1)
  }

  /** Node 622
    * Segment Id for this node is: 198
    * Starting at 0xe4e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s622(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x1234

    requires s0.stack[8] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1234;
      assert s1.Peek(8) == 0x104;
      var s2 := Push2(s1, 0x0e58);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x139d);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s623(s6, gas - 1)
  }

  /** Node 623
    * Segment Id for this node is: 253
    * Starting at 0x139d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s623(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xe58

    requires s0.stack[7] == 0x1234

    requires s0.stack[11] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe58;
      assert s1.Peek(7) == 0x1234;
      assert s1.Peek(11) == 0x104;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xe58;
      assert s11.Peek(8) == 0x1234;
      assert s11.Peek(12) == 0x104;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s624(s15, gas - 1)
  }

  /** Node 624
    * Segment Id for this node is: 199
    * Starting at 0xe58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s624(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x1234

    requires s0.stack[9] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1234;
      assert s1.Peek(9) == 0x104;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0e68);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x1459);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s625(s11, gas - 1)
  }

  /** Node 625
    * Segment Id for this node is: 266
    * Starting at 0x1459
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s625(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1459 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xe68

    requires s0.stack[8] == 0x1234

    requires s0.stack[12] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe68;
      assert s1.Peek(8) == 0x1234;
      assert s1.Peek(12) == 0x104;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s626(s2, gas - 1)
  }

  /** Node 626
    * Segment Id for this node is: 267
    * Starting at 0x145c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s626(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x145c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xe68

    requires s0.stack[9] == 0x1234

    requires s0.stack[13] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe68;
      assert s1.Peek(9) == 0x1234;
      assert s1.Peek(13) == 0x104;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x1477);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s628(s7, gas - 1)
      else
        ExecuteFromCFGNode_s627(s7, gas - 1)
  }

  /** Node 627
    * Segment Id for this node is: 268
    * Starting at 0x1465
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s627(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1465 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xe68

    requires s0.stack[9] == 0x1234

    requires s0.stack[13] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xe68;
      assert s1.Peek(10) == 0x1234;
      assert s1.Peek(14) == 0x104;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0xe68;
      assert s11.Peek(10) == 0x1234;
      assert s11.Peek(14) == 0x104;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x145c);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s626(s15, gas - 1)
  }

  /** Node 628
    * Segment Id for this node is: 269
    * Starting at 0x1477
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s628(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1477 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xe68

    requires s0.stack[9] == 0x1234

    requires s0.stack[13] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe68;
      assert s1.Peek(9) == 0x1234;
      assert s1.Peek(13) == 0x104;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x1486);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s630(s7, gas - 1)
      else
        ExecuteFromCFGNode_s629(s7, gas - 1)
  }

  /** Node 629
    * Segment Id for this node is: 270
    * Starting at 0x1480
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s629(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1480 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xe68

    requires s0.stack[9] == 0x1234

    requires s0.stack[13] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xe68;
      assert s1.Peek(10) == 0x1234;
      assert s1.Peek(14) == 0x104;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s630(s5, gas - 1)
  }

  /** Node 630
    * Segment Id for this node is: 271
    * Starting at 0x1486
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s630(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1486 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xe68

    requires s0.stack[9] == 0x1234

    requires s0.stack[13] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe68;
      assert s1.Peek(9) == 0x1234;
      assert s1.Peek(13) == 0x104;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s631(s6, gas - 1)
  }

  /** Node 631
    * Segment Id for this node is: 200
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s631(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x1234

    requires s0.stack[8] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1234;
      assert s1.Peek(8) == 0x104;
      var s2 := Push2(s1, 0x0e71);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x151c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s632(s5, gas - 1)
  }

  /** Node 632
    * Segment Id for this node is: 280
    * Starting at 0x151c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s632(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xe71

    requires s0.stack[6] == 0x1234

    requires s0.stack[10] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe71;
      assert s1.Peek(6) == 0x1234;
      assert s1.Peek(10) == 0x104;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xe71;
      assert s11.Peek(7) == 0x1234;
      assert s11.Peek(11) == 0x104;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s633(s14, gas - 1)
  }

  /** Node 633
    * Segment Id for this node is: 201
    * Starting at 0xe71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s633(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x1234

    requires s0.stack[9] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1234;
      assert s1.Peek(9) == 0x104;
      var s2 := Dup5(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s634(s11, gas - 1)
  }

  /** Node 634
    * Segment Id for this node is: 229
    * Starting at 0x1234
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s634(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1234 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x104

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x104;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s635(s8, gas - 1)
  }

  /** Node 635
    * Segment Id for this node is: 26
    * Starting at 0x104
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s635(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104 as nat
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

  /** Node 636
    * Segment Id for this node is: 77
    * Starting at 0x358
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s636(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x358 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xf7;
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
      ExecuteFromCFGNode_s637(s11, gas - 1)
  }

  /** Node 637
    * Segment Id for this node is: 78
    * Starting at 0x366
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s637(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x366 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xf7;
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
      assert s11.Peek(7) == 0xf7;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x0366);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s637(s16, gas - 1)
      else
        ExecuteFromCFGNode_s638(s16, gas - 1)
  }

  /** Node 638
    * Segment Id for this node is: 79
    * Starting at 0x37a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s638(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0xf7;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s617(s8, gas - 1)
  }

  /** Node 639
    * Segment Id for this node is: 23
    * Starting at 0xea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s639(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
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
