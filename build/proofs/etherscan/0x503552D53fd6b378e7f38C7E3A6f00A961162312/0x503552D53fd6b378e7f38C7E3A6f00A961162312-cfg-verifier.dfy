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
      var s7 := Push2(s6, 0x0059);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s8, gas - 1)
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
      var s6 := Push4(s5, 0x57ea89b6);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x0065);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s184(s9, gas - 1)
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
      var s2 := Push4(s1, 0xb64273d3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x007c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s181(s5, gas - 1)
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
      var s2 := Push4(s1, 0xbedf0f4a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x009f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s5, gas - 1)
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
      var s2 := Push4(s1, 0xd007b811);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00bb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s5, gas - 1)
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
      var s2 := Push4(s1, 0xdfa5a437);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00c3);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s157(s5, gas - 1)
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
      var s2 := Push4(s1, 0xf39d8c65);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00e3);
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
    * Segment Id for this node is: 26
    * Starting at 0xe3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3 as nat
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
      var s5 := Push2(s4, 0x00ef);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s6, gas - 1)
      else
        ExecuteFromCFGNode_s9(s6, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 27
    * Starting at 0xeb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb as nat
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
    * Segment Id for this node is: 28
    * Starting at 0xef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00f8);
      var s4 := Push2(s3, 0x017f);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 37
    * Starting at 0x17f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf8;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x018b);
      var s5 := Push2(s4, 0x02e7);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s6, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 54
    * Starting at 0x2e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x18b

    requires s0.stack[2] == 0x60

    requires s0.stack[3] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x18b;
      assert s1.Peek(2) == 0x60;
      assert s1.Peek(3) == 0xf8;
      var s2 := Push1(s1, 0x03);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup1(s4);
      var s6 := SLoad(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Swap3(s7);
      var s9 := Push2(s8, 0x0304);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(3) == 0x304;
      assert s11.Peek(5) == 0x60;
      assert s11.Peek(6) == 0x18b;
      assert s11.Peek(8) == 0x60;
      assert s11.Peek(9) == 0xf8;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := And(s15);
      var s17 := Balance(s16);
      var s18 := Push2(s17, 0x0575);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s19, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 100
    * Starting at 0x575
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x575 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x304

    requires s0.stack[4] == 0x60

    requires s0.stack[5] == 0x18b

    requires s0.stack[7] == 0x60

    requires s0.stack[8] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x304;
      assert s1.Peek(4) == 0x60;
      assert s1.Peek(5) == 0x18b;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(8) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0587);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s8, gas - 1)
      else
        ExecuteFromCFGNode_s14(s8, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 101
    * Starting at 0x580
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x580 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x304

    requires s0.stack[5] == 0x60

    requires s0.stack[6] == 0x18b

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0587);
      assert s1.Peek(0) == 0x587;
      assert s1.Peek(4) == 0x304;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(7) == 0x18b;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0xf8;
      var s2 := Push2(s1, 0x05eb);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s3, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 115
    * Starting at 0x5eb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x587

    requires s0.stack[4] == 0x304

    requires s0.stack[6] == 0x60

    requires s0.stack[7] == 0x18b

    requires s0.stack[9] == 0x60

    requires s0.stack[10] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x587;
      assert s1.Peek(4) == 0x304;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(7) == 0x18b;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0xf8;
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
      assert s11.Peek(2) == 0x587;
      assert s11.Peek(6) == 0x304;
      assert s11.Peek(8) == 0x60;
      assert s11.Peek(9) == 0x18b;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(12) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 16
    * Segment Id for this node is: 102
    * Starting at 0x587
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x587 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x304

    requires s0.stack[5] == 0x60

    requires s0.stack[6] == 0x18b

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x304;
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(6) == 0x18b;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Sub(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s5, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 55
    * Starting at 0x304
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x60

    requires s0.stack[3] == 0x18b

    requires s0.stack[5] == 0x60

    requires s0.stack[6] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x60;
      assert s1.Peek(3) == 0x18b;
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(6) == 0xf8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := PushN(s3, 5, 0xd127b3abcd);
      var s5 := Push1(s4, 0x00);
      var s6 := PushN(s5, 5, 0xe8d4a51000);
      var s7 := Push2(s6, 0x031e);
      var s8 := Dup4(s7);
      var s9 := Dup6(s8);
      var s10 := Push2(s9, 0x0556);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s11, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 97
    * Starting at 0x556
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x556 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x31e

    requires s0.stack[7] == 0x60

    requires s0.stack[8] == 0x18b

    requires s0.stack[10] == 0x60

    requires s0.stack[11] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31e;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(8) == 0x18b;
      assert s1.Peek(10) == 0x60;
      assert s1.Peek(11) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Not(s4);
      var s6 := Div(s5);
      var s7 := Dup4(s6);
      var s8 := Gt(s7);
      var s9 := Dup3(s8);
      var s10 := IsZero(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(5) == 0x31e;
      assert s11.Peek(10) == 0x60;
      assert s11.Peek(11) == 0x18b;
      assert s11.Peek(13) == 0x60;
      assert s11.Peek(14) == 0xf8;
      var s12 := And(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x0570);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s15, gas - 1)
      else
        ExecuteFromCFGNode_s19(s15, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 98
    * Starting at 0x569
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x569 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x31e

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0x18b

    requires s0.stack[11] == 0x60

    requires s0.stack[12] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0570);
      assert s1.Peek(0) == 0x570;
      assert s1.Peek(4) == 0x31e;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0x18b;
      assert s1.Peek(12) == 0x60;
      assert s1.Peek(13) == 0xf8;
      var s2 := Push2(s1, 0x05eb);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s3, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 115
    * Starting at 0x5eb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x570

    requires s0.stack[4] == 0x31e

    requires s0.stack[9] == 0x60

    requires s0.stack[10] == 0x18b

    requires s0.stack[12] == 0x60

    requires s0.stack[13] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x570;
      assert s1.Peek(4) == 0x31e;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0x18b;
      assert s1.Peek(12) == 0x60;
      assert s1.Peek(13) == 0xf8;
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
      assert s11.Peek(2) == 0x570;
      assert s11.Peek(6) == 0x31e;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(12) == 0x18b;
      assert s11.Peek(14) == 0x60;
      assert s11.Peek(15) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 21
    * Segment Id for this node is: 99
    * Starting at 0x570
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x570 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x31e

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0x18b

    requires s0.stack[11] == 0x60

    requires s0.stack[12] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x31e;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0x18b;
      assert s1.Peek(11) == 0x60;
      assert s1.Peek(12) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Mul(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s5, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 56
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x60

    requires s0.stack[6] == 0x18b

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(6) == 0x18b;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0xf8;
      var s2 := Push2(s1, 0x0328);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0542);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s6, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 94
    * Starting at 0x542
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x542 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x328

    requires s0.stack[6] == 0x60

    requires s0.stack[7] == 0x18b

    requires s0.stack[9] == 0x60

    requires s0.stack[10] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x328;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(7) == 0x18b;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0551);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s26(s5, gas - 1)
      else
        ExecuteFromCFGNode_s24(s5, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 95
    * Starting at 0x54a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x328

    requires s0.stack[7] == 0x60

    requires s0.stack[8] == 0x18b

    requires s0.stack[10] == 0x60

    requires s0.stack[11] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0551);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x328;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0x18b;
      assert s1.Peek(11) == 0x60;
      assert s1.Peek(12) == 0xf8;
      var s2 := Push2(s1, 0x0601);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s3, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 116
    * Starting at 0x601
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x601 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x551

    requires s0.stack[4] == 0x328

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0x18b

    requires s0.stack[11] == 0x60

    requires s0.stack[12] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x328;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0x18b;
      assert s1.Peek(11) == 0x60;
      assert s1.Peek(12) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x12);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x551;
      assert s11.Peek(6) == 0x328;
      assert s11.Peek(10) == 0x60;
      assert s11.Peek(11) == 0x18b;
      assert s11.Peek(13) == 0x60;
      assert s11.Peek(14) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 26
    * Segment Id for this node is: 96
    * Starting at 0x551
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x551 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x328

    requires s0.stack[7] == 0x60

    requires s0.stack[8] == 0x18b

    requires s0.stack[10] == 0x60

    requires s0.stack[11] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x328;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(8) == 0x18b;
      assert s1.Peek(10) == 0x60;
      assert s1.Peek(11) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s5, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 57
    * Starting at 0x328
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x328 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x60

    requires s0.stack[5] == 0x18b

    requires s0.stack[7] == 0x60

    requires s0.stack[8] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60;
      assert s1.Peek(5) == 0x18b;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(8) == 0xf8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push2(s4, 0x033e);
      var s6 := Push8(s5, 0x0de0b6b3a7640000);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0542);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s9, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 94
    * Starting at 0x542
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x542 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x33e

    requires s0.stack[7] == 0x60

    requires s0.stack[8] == 0x18b

    requires s0.stack[10] == 0x60

    requires s0.stack[11] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x33e;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(8) == 0x18b;
      assert s1.Peek(10) == 0x60;
      assert s1.Peek(11) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0551);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s5, gas - 1)
      else
        ExecuteFromCFGNode_s29(s5, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 95
    * Starting at 0x54a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x33e

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0x18b

    requires s0.stack[11] == 0x60

    requires s0.stack[12] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0551);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x33e;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0x18b;
      assert s1.Peek(12) == 0x60;
      assert s1.Peek(13) == 0xf8;
      var s2 := Push2(s1, 0x0601);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s3, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 116
    * Starting at 0x601
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x601 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x551

    requires s0.stack[4] == 0x33e

    requires s0.stack[9] == 0x60

    requires s0.stack[10] == 0x18b

    requires s0.stack[12] == 0x60

    requires s0.stack[13] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x33e;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0x18b;
      assert s1.Peek(12) == 0x60;
      assert s1.Peek(13) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x12);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x551;
      assert s11.Peek(6) == 0x33e;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(12) == 0x18b;
      assert s11.Peek(14) == 0x60;
      assert s11.Peek(15) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 31
    * Segment Id for this node is: 96
    * Starting at 0x551
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x551 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x33e

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0x18b

    requires s0.stack[11] == 0x60

    requires s0.stack[12] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33e;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0x18b;
      assert s1.Peek(11) == 0x60;
      assert s1.Peek(12) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s5, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 58
    * Starting at 0x33e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x60

    requires s0.stack[6] == 0x18b

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(6) == 0x18b;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0xf8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push2(s4, 0x0354);
      var s6 := Push8(s5, 0x0de0b6b3a7640000);
      var s7 := Dup5(s6);
      var s8 := Push2(s7, 0x05d7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s9, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 112
    * Starting at 0x5d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x354

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0x18b

    requires s0.stack[11] == 0x60

    requires s0.stack[12] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x354;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0x18b;
      assert s1.Peek(11) == 0x60;
      assert s1.Peek(12) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x05e6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s5, gas - 1)
      else
        ExecuteFromCFGNode_s34(s5, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 113
    * Starting at 0x5df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x354

    requires s0.stack[9] == 0x60

    requires s0.stack[10] == 0x18b

    requires s0.stack[12] == 0x60

    requires s0.stack[13] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05e6);
      assert s1.Peek(0) == 0x5e6;
      assert s1.Peek(4) == 0x354;
      assert s1.Peek(10) == 0x60;
      assert s1.Peek(11) == 0x18b;
      assert s1.Peek(13) == 0x60;
      assert s1.Peek(14) == 0xf8;
      var s2 := Push2(s1, 0x0601);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s3, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 116
    * Starting at 0x601
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x601 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x5e6

    requires s0.stack[4] == 0x354

    requires s0.stack[10] == 0x60

    requires s0.stack[11] == 0x18b

    requires s0.stack[13] == 0x60

    requires s0.stack[14] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5e6;
      assert s1.Peek(4) == 0x354;
      assert s1.Peek(10) == 0x60;
      assert s1.Peek(11) == 0x18b;
      assert s1.Peek(13) == 0x60;
      assert s1.Peek(14) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x12);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x5e6;
      assert s11.Peek(6) == 0x354;
      assert s11.Peek(12) == 0x60;
      assert s11.Peek(13) == 0x18b;
      assert s11.Peek(15) == 0x60;
      assert s11.Peek(16) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 36
    * Segment Id for this node is: 114
    * Starting at 0x5e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x354

    requires s0.stack[9] == 0x60

    requires s0.stack[10] == 0x18b

    requires s0.stack[12] == 0x60

    requires s0.stack[13] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x354;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0x18b;
      assert s1.Peek(12) == 0x60;
      assert s1.Peek(13) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Mod(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s5, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 59
    * Starting at 0x354
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x354 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x60

    requires s0.stack[7] == 0x18b

    requires s0.stack[9] == 0x60

    requires s0.stack[10] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(7) == 0x18b;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0xf8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x037e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s112(s9, gas - 1)
      else
        ExecuteFromCFGNode_s38(s9, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 60
    * Starting at 0x360
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x360 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x60

    requires s0.stack[7] == 0x18b

    requires s0.stack[9] == 0x60

    requires s0.stack[10] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(8) == 0x18b;
      assert s1.Peek(10) == 0x60;
      assert s1.Peek(11) == 0xf8;
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MStore(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(8) == 0x60;
      assert s11.Peek(9) == 0x18b;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(12) == 0xf8;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Push1(s13, 0x03);
      var s15 := Push1(s14, 0xfc);
      var s16 := Shl(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Pop(s18);
      var s20 := Push2(s19, 0x0387);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s21, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 62
    * Starting at 0x387
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x387 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x60

    requires s0.stack[8] == 0x18b

    requires s0.stack[10] == 0x60

    requires s0.stack[11] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(8) == 0x18b;
      assert s1.Peek(10) == 0x60;
      assert s1.Peek(11) == 0xf8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push2(s4, 0x0394);
      var s6 := Dup4(s5);
      var s7 := Push2(s6, 0x03c4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s8, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 65
    * Starting at 0x3c4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x394

    requires s0.stack[9] == 0x60

    requires s0.stack[10] == 0x18b

    requires s0.stack[12] == 0x60

    requires s0.stack[13] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x394;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0x18b;
      assert s1.Peek(12) == 0x60;
      assert s1.Peek(13) == 0xf8;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x0a);
      var s4 := Dup3(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s41(s5, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 66
    * Starting at 0x3cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x60

    requires s0.stack[5] == 0x394

    requires s0.stack[13] == 0x60

    requires s0.stack[14] == 0x18b

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x60;
      assert s1.Peek(5) == 0x394;
      assert s1.Peek(13) == 0x60;
      assert s1.Peek(14) == 0x18b;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0xf8;
      var s2 := Dup1(s1);
      var s3 := Push2(s2, 0x03d6);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x05bc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s6, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 109
    * Starting at 0x5bc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x3d6

    requires s0.stack[6] == 0x60

    requires s0.stack[8] == 0x394

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3d6;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(8) == 0x394;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x00);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x05d0);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s9, gas - 1)
      else
        ExecuteFromCFGNode_s43(s9, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 110
    * Starting at 0x5c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0x3d6

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x394

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05d0);
      assert s1.Peek(0) == 0x5d0;
      assert s1.Peek(3) == 0x3d6;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x394;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push2(s1, 0x05eb);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s3, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 115
    * Starting at 0x5eb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x5d0

    requires s0.stack[3] == 0x3d6

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5d0;
      assert s1.Peek(3) == 0x3d6;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x394;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
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
      assert s11.Peek(2) == 0x5d0;
      assert s11.Peek(5) == 0x3d6;
      assert s11.Peek(10) == 0x60;
      assert s11.Peek(12) == 0x394;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0x18b;
      assert s11.Peek(23) == 0x60;
      assert s11.Peek(24) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 45
    * Segment Id for this node is: 111
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0x3d6

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x394

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3d6;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x394;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s6, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 67
    * Starting at 0x3d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x394

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x394;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x03e4);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Dup4(s7);
      var s9 := Push2(s8, 0x0542);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s10, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 94
    * Starting at 0x542
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x542 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x3e4

    requires s0.stack[6] == 0x60

    requires s0.stack[8] == 0x394

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3e4;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(8) == 0x394;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0551);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s5, gas - 1)
      else
        ExecuteFromCFGNode_s48(s5, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 95
    * Starting at 0x54a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x3e4

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x394

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0551);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x3e4;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x394;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push2(s1, 0x0601);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s3, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 116
    * Starting at 0x601
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x601 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x551

    requires s0.stack[4] == 0x3e4

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x3e4;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x394;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x12);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x551;
      assert s11.Peek(6) == 0x3e4;
      assert s11.Peek(10) == 0x60;
      assert s11.Peek(12) == 0x394;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0x18b;
      assert s11.Peek(23) == 0x60;
      assert s11.Peek(24) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 50
    * Segment Id for this node is: 96
    * Starting at 0x551
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x551 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x3e4

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x394

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e4;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x394;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s5, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 68
    * Starting at 0x3e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x60

    requires s0.stack[6] == 0x394

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60;
      assert s1.Peek(6) == 0x394;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x03cc);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s6, gas - 1)
      else
        ExecuteFromCFGNode_s52(s6, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 69
    * Starting at 0x3ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x60

    requires s0.stack[5] == 0x394

    requires s0.stack[13] == 0x60

    requires s0.stack[14] == 0x18b

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x60;
      assert s1.Peek(6) == 0x394;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Dup2(s1);
      var s3 := Push8(s2, 0xffffffffffffffff);
      var s4 := Dup2(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0406);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s8, gas - 1)
      else
        ExecuteFromCFGNode_s53(s8, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 70
    * Starting at 0x3ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x394

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0406);
      assert s1.Peek(0) == 0x406;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(8) == 0x394;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Push2(s1, 0x062d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s3, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 118
    * Starting at 0x62d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x406

    requires s0.stack[6] == 0x60

    requires s0.stack[8] == 0x394

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x406;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(8) == 0x394;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x406;
      assert s11.Peek(8) == 0x60;
      assert s11.Peek(10) == 0x394;
      assert s11.Peek(18) == 0x60;
      assert s11.Peek(19) == 0x18b;
      assert s11.Peek(21) == 0x60;
      assert s11.Peek(22) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 55
    * Segment Id for this node is: 71
    * Starting at 0x406
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x406 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x394

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x394;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(8) == 0x60;
      assert s11.Peek(10) == 0x394;
      assert s11.Peek(18) == 0x60;
      assert s11.Peek(19) == 0x18b;
      assert s11.Peek(21) == 0x60;
      assert s11.Peek(22) == 0xf8;
      var s12 := Not(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0x60;
      assert s21.Peek(9) == 0x394;
      assert s21.Peek(17) == 0x60;
      assert s21.Peek(18) == 0x18b;
      assert s21.Peek(20) == 0x60;
      assert s21.Peek(21) == 0xf8;
      var s22 := Push2(s21, 0x0430);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s23, gas - 1)
      else
        ExecuteFromCFGNode_s56(s23, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 72
    * Starting at 0x424
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x424 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x60

    requires s0.stack[8] == 0x394

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x394;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup2(s3);
      var s5 := Dup1(s4);
      var s6 := CallDataSize(s5);
      var s7 := Dup4(s6);
      var s8 := CallDataCopy(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s57(s11, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 73
    * Starting at 0x430
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x430 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x60

    requires s0.stack[8] == 0x394

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(8) == 0x394;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s58(s4, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 74
    * Starting at 0x434
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x434 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x60

    requires s0.stack[6] == 0x394

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60;
      assert s1.Peek(6) == 0x394;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Dup6(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0499);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s5, gas - 1)
      else
        ExecuteFromCFGNode_s59(s5, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 75
    * Starting at 0x43b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x60

    requires s0.stack[6] == 0x394

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0445);
      assert s1.Peek(0) == 0x445;
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x394;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0575);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s5, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 100
    * Starting at 0x575
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x575 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0x445

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x394

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x445;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x394;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0587);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s8, gas - 1)
      else
        ExecuteFromCFGNode_s61(s8, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 101
    * Starting at 0x580
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x580 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0587);
      assert s1.Peek(0) == 0x587;
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x394;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Push2(s1, 0x05eb);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s3, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 115
    * Starting at 0x5eb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[0] == 0x587

    requires s0.stack[4] == 0x445

    requires s0.stack[9] == 0x60

    requires s0.stack[11] == 0x394

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0x18b

    requires s0.stack[22] == 0x60

    requires s0.stack[23] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x587;
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x394;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
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
      assert s11.Peek(2) == 0x587;
      assert s11.Peek(6) == 0x445;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(13) == 0x394;
      assert s11.Peek(21) == 0x60;
      assert s11.Peek(22) == 0x18b;
      assert s11.Peek(24) == 0x60;
      assert s11.Peek(25) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 63
    * Segment Id for this node is: 102
    * Starting at 0x587
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x587 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x445;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x394;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Sub(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s5, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 76
    * Starting at 0x445
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x445 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x394

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x394;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0451);
      var s5 := Dup5(s4);
      var s6 := Dup8(s5);
      var s7 := Push2(s6, 0x05d7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s8, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 112
    * Starting at 0x5d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0x451

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x394

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x451;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x394;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x05e6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s5, gas - 1)
      else
        ExecuteFromCFGNode_s66(s5, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 113
    * Starting at 0x5df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0x451

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05e6);
      assert s1.Peek(0) == 0x5e6;
      assert s1.Peek(4) == 0x451;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x394;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Push2(s1, 0x0601);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s3, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 116
    * Starting at 0x601
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x601 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[0] == 0x5e6

    requires s0.stack[4] == 0x451

    requires s0.stack[9] == 0x60

    requires s0.stack[11] == 0x394

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0x18b

    requires s0.stack[22] == 0x60

    requires s0.stack[23] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5e6;
      assert s1.Peek(4) == 0x451;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x394;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x12);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x5e6;
      assert s11.Peek(6) == 0x451;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(13) == 0x394;
      assert s11.Peek(21) == 0x60;
      assert s11.Peek(22) == 0x18b;
      assert s11.Peek(24) == 0x60;
      assert s11.Peek(25) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 68
    * Segment Id for this node is: 114
    * Starting at 0x5e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0x451

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x451;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x394;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Mod(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s5, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 77
    * Starting at 0x451
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x451 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x394

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x394;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Push2(s1, 0x045c);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x30);
      var s5 := Push2(s4, 0x052a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s6, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 91
    * Starting at 0x52a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0x45c

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x394

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x45c;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x394;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x053d);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s9, gas - 1)
      else
        ExecuteFromCFGNode_s71(s9, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 92
    * Starting at 0x536
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0x45c

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x053d);
      assert s1.Peek(0) == 0x53d;
      assert s1.Peek(4) == 0x45c;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x394;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Push2(s1, 0x05eb);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s3, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 115
    * Starting at 0x5eb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[0] == 0x53d

    requires s0.stack[4] == 0x45c

    requires s0.stack[9] == 0x60

    requires s0.stack[11] == 0x394

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0x18b

    requires s0.stack[22] == 0x60

    requires s0.stack[23] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x53d;
      assert s1.Peek(4) == 0x45c;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x394;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
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
      assert s11.Peek(2) == 0x53d;
      assert s11.Peek(6) == 0x45c;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(13) == 0x394;
      assert s11.Peek(21) == 0x60;
      assert s11.Peek(22) == 0x18b;
      assert s11.Peek(24) == 0x60;
      assert s11.Peek(25) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 73
    * Segment Id for this node is: 93
    * Starting at 0x53d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0x45c

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x45c;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x394;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s5, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 78
    * Starting at 0x45c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x394

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x394;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Push1(s1, 0xf8);
      var s3 := Shl(s2);
      var s4 := Dup2(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := Push2(s9, 0x0471);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s75(s11, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 79
    * Starting at 0x46a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x394

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0471);
      assert s1.Peek(0) == 0x471;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x394;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push2(s1, 0x0617);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s3, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 117
    * Starting at 0x617
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x617 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x471

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x471;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x394;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x471;
      assert s11.Peek(10) == 0x60;
      assert s11.Peek(12) == 0x394;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0x18b;
      assert s11.Peek(23) == 0x60;
      assert s11.Peek(24) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 77
    * Segment Id for this node is: 80
    * Starting at 0x471
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x471 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x394

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x394;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xf8);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Not(s10);
      assert s11.Peek(7) == 0x60;
      assert s11.Peek(9) == 0x394;
      assert s11.Peek(17) == 0x60;
      assert s11.Peek(18) == 0x18b;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0xf8;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push2(s19, 0x0492);
      var s21 := Dup5(s20);
      assert s21.Peek(1) == 0x492;
      assert s21.Peek(6) == 0x60;
      assert s21.Peek(8) == 0x394;
      assert s21.Peek(16) == 0x60;
      assert s21.Peek(17) == 0x18b;
      assert s21.Peek(19) == 0x60;
      assert s21.Peek(20) == 0xf8;
      var s22 := Dup8(s21);
      var s23 := Push2(s22, 0x0542);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s24, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 94
    * Starting at 0x542
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x542 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0x492

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x394

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x492;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x394;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0551);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s5, gas - 1)
      else
        ExecuteFromCFGNode_s79(s5, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 95
    * Starting at 0x54a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0x492

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0551);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x492;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x394;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Push2(s1, 0x0601);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s3, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 116
    * Starting at 0x601
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x601 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[0] == 0x551

    requires s0.stack[4] == 0x492

    requires s0.stack[9] == 0x60

    requires s0.stack[11] == 0x394

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0x18b

    requires s0.stack[22] == 0x60

    requires s0.stack[23] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x492;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x394;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x12);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x551;
      assert s11.Peek(6) == 0x492;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(13) == 0x394;
      assert s11.Peek(21) == 0x60;
      assert s11.Peek(22) == 0x18b;
      assert s11.Peek(24) == 0x60;
      assert s11.Peek(25) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 81
    * Segment Id for this node is: 96
    * Starting at 0x551
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x551 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0x492

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x394

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x492;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x394;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s5, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 81
    * Starting at 0x492
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x394

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x394;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Swap6(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0434);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s5, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 82
    * Starting at 0x499
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x499 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x60

    requires s0.stack[6] == 0x394

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60;
      assert s1.Peek(6) == 0x394;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s9, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 63
    * Starting at 0x394
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x394 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0x18b

    requires s0.stack[11] == 0x60

    requires s0.stack[12] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0x18b;
      assert s1.Peek(11) == 0x60;
      assert s1.Peek(12) == 0xf8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03a9);
      var s11 := Swap3(s10);
      assert s11.Peek(3) == 0x3a9;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(12) == 0x18b;
      assert s11.Peek(14) == 0x60;
      assert s11.Peek(15) == 0xf8;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x04bb);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s15, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 86
    * Starting at 0x4bb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x3a9

    requires s0.stack[11] == 0x60

    requires s0.stack[12] == 0x18b

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3a9;
      assert s1.Peek(11) == 0x60;
      assert s1.Peek(12) == 0x18b;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup4(s2);
      var s4 := MLoad(s3);
      var s5 := Push2(s4, 0x04cd);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup9(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x058c);
      assert s11.Peek(0) == 0x58c;
      assert s11.Peek(4) == 0x4cd;
      assert s11.Peek(10) == 0x3a9;
      assert s11.Peek(18) == 0x60;
      assert s11.Peek(19) == 0x18b;
      assert s11.Peek(21) == 0x60;
      assert s11.Peek(22) == 0xf8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s12, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 103
    * Starting at 0x58c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x4cd

    requires s0.stack[9] == 0x3a9

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4cd;
      assert s1.Peek(9) == 0x3a9;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s87(s2, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 104
    * Starting at 0x58f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[4] == 0x4cd

    requires s0.stack[10] == 0x3a9

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4cd;
      assert s1.Peek(10) == 0x3a9;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x05a7);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s7, gas - 1)
      else
        ExecuteFromCFGNode_s88(s7, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 105
    * Starting at 0x598
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x598 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[4] == 0x4cd

    requires s0.stack[10] == 0x3a9

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x4cd;
      assert s1.Peek(11) == 0x3a9;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x058f);
      assert s11.Peek(0) == 0x58f;
      assert s11.Peek(5) == 0x4cd;
      assert s11.Peek(11) == 0x3a9;
      assert s11.Peek(19) == 0x60;
      assert s11.Peek(20) == 0x18b;
      assert s11.Peek(22) == 0x60;
      assert s11.Peek(23) == 0xf8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s12, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 106
    * Starting at 0x5a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[4] == 0x4cd

    requires s0.stack[10] == 0x3a9

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4cd;
      assert s1.Peek(10) == 0x3a9;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x05b6);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s91(s7, gas - 1)
      else
        ExecuteFromCFGNode_s90(s7, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 107
    * Starting at 0x5b0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[4] == 0x4cd

    requires s0.stack[10] == 0x3a9

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x4cd;
      assert s1.Peek(11) == 0x3a9;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s91(s5, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 108
    * Starting at 0x5b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[4] == 0x4cd

    requires s0.stack[10] == 0x3a9

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4cd;
      assert s1.Peek(10) == 0x3a9;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s6, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 87
    * Starting at 0x4cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x3a9

    requires s0.stack[13] == 0x60

    requires s0.stack[14] == 0x18b

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a9;
      assert s1.Peek(13) == 0x60;
      assert s1.Peek(14) == 0x18b;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0xf8;
      var s2 := Push1(s1, 0x17);
      var s3 := Push1(s2, 0xf9);
      var s4 := Shl(s3);
      var s5 := Swap1(s4);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(6) == 0x3a9;
      assert s11.Peek(14) == 0x60;
      assert s11.Peek(15) == 0x18b;
      assert s11.Peek(17) == 0x60;
      assert s11.Peek(18) == 0xf8;
      var s12 := MLoad(s11);
      var s13 := Push2(s12, 0x04eb);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Dup5(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup9(s18);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x058c);
      assert s21.Peek(0) == 0x58c;
      assert s21.Peek(4) == 0x4eb;
      assert s21.Peek(11) == 0x3a9;
      assert s21.Peek(19) == 0x60;
      assert s21.Peek(20) == 0x18b;
      assert s21.Peek(22) == 0x60;
      assert s21.Peek(23) == 0xf8;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s22, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 103
    * Starting at 0x58c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0x4eb

    requires s0.stack[10] == 0x3a9

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4eb;
      assert s1.Peek(10) == 0x3a9;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s94(s2, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 104
    * Starting at 0x58f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[4] == 0x4eb

    requires s0.stack[11] == 0x3a9

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0x18b

    requires s0.stack[22] == 0x60

    requires s0.stack[23] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4eb;
      assert s1.Peek(11) == 0x3a9;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x05a7);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s96(s7, gas - 1)
      else
        ExecuteFromCFGNode_s95(s7, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 105
    * Starting at 0x598
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x598 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[4] == 0x4eb

    requires s0.stack[11] == 0x3a9

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0x18b

    requires s0.stack[22] == 0x60

    requires s0.stack[23] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x4eb;
      assert s1.Peek(12) == 0x3a9;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0x18b;
      assert s1.Peek(23) == 0x60;
      assert s1.Peek(24) == 0xf8;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x058f);
      assert s11.Peek(0) == 0x58f;
      assert s11.Peek(5) == 0x4eb;
      assert s11.Peek(12) == 0x3a9;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0x18b;
      assert s11.Peek(23) == 0x60;
      assert s11.Peek(24) == 0xf8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s12, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 106
    * Starting at 0x5a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[4] == 0x4eb

    requires s0.stack[11] == 0x3a9

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0x18b

    requires s0.stack[22] == 0x60

    requires s0.stack[23] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4eb;
      assert s1.Peek(11) == 0x3a9;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x05b6);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s7, gas - 1)
      else
        ExecuteFromCFGNode_s97(s7, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 107
    * Starting at 0x5b0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[4] == 0x4eb

    requires s0.stack[11] == 0x3a9

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0x18b

    requires s0.stack[22] == 0x60

    requires s0.stack[23] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x4eb;
      assert s1.Peek(12) == 0x3a9;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0x18b;
      assert s1.Peek(23) == 0x60;
      assert s1.Peek(24) == 0xf8;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s98(s5, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 108
    * Starting at 0x5b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[4] == 0x4eb

    requires s0.stack[11] == 0x3a9

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0x18b

    requires s0.stack[22] == 0x60

    requires s0.stack[23] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4eb;
      assert s1.Peek(11) == 0x3a9;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0x18b;
      assert s1.Peek(22) == 0x60;
      assert s1.Peek(23) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s6, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 88
    * Starting at 0x4eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x3a9

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3a9;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Add(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Add(s3);
      var s5 := Swap5(s4);
      var s6 := Swap4(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s11, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 64
    * Starting at 0x3a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0x18b

    requires s0.stack[11] == 0x60

    requires s0.stack[12] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0x18b;
      assert s1.Peek(11) == 0x60;
      assert s1.Peek(12) == 0xf8;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(9) == 0x60;
      assert s11.Peek(10) == 0x18b;
      assert s11.Peek(12) == 0x60;
      assert s11.Peek(13) == 0xf8;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Swap(s13, 8);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(2) == 0x18b;
      assert s21.Peek(4) == 0x60;
      assert s21.Peek(5) == 0xf8;
      var s22 := Pop(s21);
      var s23 := Swap1(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s24, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 38
    * Starting at 0x18b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x60

    requires s0.stack[3] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x60;
      assert s1.Peek(3) == 0xf8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s6, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 29
    * Starting at 0xf8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0105);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x04f7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s8, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 89
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x105

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x105;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup3(s5);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup5(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x105;
      var s12 := MStore(s11);
      var s13 := Push2(s12, 0x0516);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup8(s18);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x058c);
      assert s21.Peek(0) == 0x58c;
      assert s21.Peek(4) == 0x516;
      assert s21.Peek(9) == 0x105;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s22, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 103
    * Starting at 0x58c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x516

    requires s0.stack[8] == 0x105

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x516;
      assert s1.Peek(8) == 0x105;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s105(s2, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 104
    * Starting at 0x58f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x516

    requires s0.stack[9] == 0x105

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x516;
      assert s1.Peek(9) == 0x105;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x05a7);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s7, gas - 1)
      else
        ExecuteFromCFGNode_s106(s7, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 105
    * Starting at 0x598
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x598 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x516

    requires s0.stack[9] == 0x105

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x516;
      assert s1.Peek(10) == 0x105;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x058f);
      assert s11.Peek(0) == 0x58f;
      assert s11.Peek(5) == 0x516;
      assert s11.Peek(10) == 0x105;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s12, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 106
    * Starting at 0x5a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x516

    requires s0.stack[9] == 0x105

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x516;
      assert s1.Peek(9) == 0x105;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x05b6);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s109(s7, gas - 1)
      else
        ExecuteFromCFGNode_s108(s7, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 107
    * Starting at 0x5b0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x516

    requires s0.stack[9] == 0x105

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x516;
      assert s1.Peek(10) == 0x105;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s109(s5, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 108
    * Starting at 0x5b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x516

    requires s0.stack[9] == 0x105

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x516;
      assert s1.Peek(9) == 0x105;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s6, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 90
    * Starting at 0x516
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x516 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x105

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x105;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(4) == 0x105;
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s17, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 30
    * Starting at 0x105
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105 as nat
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

  /** Node 112
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x60

    requires s0.stack[7] == 0x18b

    requires s0.stack[9] == 0x60

    requires s0.stack[10] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(7) == 0x18b;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(10) == 0xf8;
      var s2 := Push2(s1, 0x0387);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x03c4);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s5, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 65
    * Starting at 0x3c4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x387

    requires s0.stack[8] == 0x60

    requires s0.stack[9] == 0x18b

    requires s0.stack[11] == 0x60

    requires s0.stack[12] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x387;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(9) == 0x18b;
      assert s1.Peek(11) == 0x60;
      assert s1.Peek(12) == 0xf8;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x0a);
      var s4 := Dup3(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s114(s5, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 66
    * Starting at 0x3cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x60

    requires s0.stack[5] == 0x387

    requires s0.stack[12] == 0x60

    requires s0.stack[13] == 0x18b

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x60;
      assert s1.Peek(5) == 0x387;
      assert s1.Peek(12) == 0x60;
      assert s1.Peek(13) == 0x18b;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0xf8;
      var s2 := Dup1(s1);
      var s3 := Push2(s2, 0x03d6);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x05bc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s6, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 109
    * Starting at 0x5bc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x3d6

    requires s0.stack[6] == 0x60

    requires s0.stack[8] == 0x387

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3d6;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(8) == 0x387;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x00);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x05d0);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s9, gas - 1)
      else
        ExecuteFromCFGNode_s116(s9, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 110
    * Starting at 0x5c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x3d6

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x387

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05d0);
      assert s1.Peek(0) == 0x5d0;
      assert s1.Peek(3) == 0x3d6;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x387;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push2(s1, 0x05eb);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s3, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 115
    * Starting at 0x5eb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x5d0

    requires s0.stack[3] == 0x3d6

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5d0;
      assert s1.Peek(3) == 0x3d6;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x387;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
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
      assert s11.Peek(2) == 0x5d0;
      assert s11.Peek(5) == 0x3d6;
      assert s11.Peek(10) == 0x60;
      assert s11.Peek(12) == 0x387;
      assert s11.Peek(19) == 0x60;
      assert s11.Peek(20) == 0x18b;
      assert s11.Peek(22) == 0x60;
      assert s11.Peek(23) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 118
    * Segment Id for this node is: 111
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x3d6

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x387

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3d6;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x387;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s6, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 67
    * Starting at 0x3d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x387

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x387;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x03e4);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Dup4(s7);
      var s9 := Push2(s8, 0x0542);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s10, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 94
    * Starting at 0x542
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x542 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x3e4

    requires s0.stack[6] == 0x60

    requires s0.stack[8] == 0x387

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3e4;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(8) == 0x387;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0551);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s5, gas - 1)
      else
        ExecuteFromCFGNode_s121(s5, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 95
    * Starting at 0x54a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x3e4

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x387

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0551);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x3e4;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x387;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push2(s1, 0x0601);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s3, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 116
    * Starting at 0x601
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x601 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x551

    requires s0.stack[4] == 0x3e4

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x3e4;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x387;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x12);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x551;
      assert s11.Peek(6) == 0x3e4;
      assert s11.Peek(10) == 0x60;
      assert s11.Peek(12) == 0x387;
      assert s11.Peek(19) == 0x60;
      assert s11.Peek(20) == 0x18b;
      assert s11.Peek(22) == 0x60;
      assert s11.Peek(23) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 123
    * Segment Id for this node is: 96
    * Starting at 0x551
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x551 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x3e4

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x387

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e4;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x387;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s5, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 68
    * Starting at 0x3e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x60

    requires s0.stack[6] == 0x387

    requires s0.stack[13] == 0x60

    requires s0.stack[14] == 0x18b

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60;
      assert s1.Peek(6) == 0x387;
      assert s1.Peek(13) == 0x60;
      assert s1.Peek(14) == 0x18b;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0xf8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x03cc);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s6, gas - 1)
      else
        ExecuteFromCFGNode_s125(s6, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 69
    * Starting at 0x3ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x60

    requires s0.stack[5] == 0x387

    requires s0.stack[12] == 0x60

    requires s0.stack[13] == 0x18b

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x60;
      assert s1.Peek(6) == 0x387;
      assert s1.Peek(13) == 0x60;
      assert s1.Peek(14) == 0x18b;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0xf8;
      var s2 := Dup2(s1);
      var s3 := Push8(s2, 0xffffffffffffffff);
      var s4 := Dup2(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0406);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s128(s8, gas - 1)
      else
        ExecuteFromCFGNode_s126(s8, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 70
    * Starting at 0x3ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x387

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0406);
      assert s1.Peek(0) == 0x406;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(8) == 0x387;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Push2(s1, 0x062d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s3, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 118
    * Starting at 0x62d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x406

    requires s0.stack[6] == 0x60

    requires s0.stack[8] == 0x387

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x406;
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(8) == 0x387;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x406;
      assert s11.Peek(8) == 0x60;
      assert s11.Peek(10) == 0x387;
      assert s11.Peek(17) == 0x60;
      assert s11.Peek(18) == 0x18b;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 128
    * Segment Id for this node is: 71
    * Starting at 0x406
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x406 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x387

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x387;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(8) == 0x60;
      assert s11.Peek(10) == 0x387;
      assert s11.Peek(17) == 0x60;
      assert s11.Peek(18) == 0x18b;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0xf8;
      var s12 := Not(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0x60;
      assert s21.Peek(9) == 0x387;
      assert s21.Peek(16) == 0x60;
      assert s21.Peek(17) == 0x18b;
      assert s21.Peek(19) == 0x60;
      assert s21.Peek(20) == 0xf8;
      var s22 := Push2(s21, 0x0430);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s23, gas - 1)
      else
        ExecuteFromCFGNode_s129(s23, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 72
    * Starting at 0x424
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x424 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x60

    requires s0.stack[8] == 0x387

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x387;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup2(s3);
      var s5 := Dup1(s4);
      var s6 := CallDataSize(s5);
      var s7 := Dup4(s6);
      var s8 := CallDataCopy(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s130(s11, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 73
    * Starting at 0x430
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x430 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x60

    requires s0.stack[8] == 0x387

    requires s0.stack[15] == 0x60

    requires s0.stack[16] == 0x18b

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x60;
      assert s1.Peek(8) == 0x387;
      assert s1.Peek(15) == 0x60;
      assert s1.Peek(16) == 0x18b;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s131(s4, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 74
    * Starting at 0x434
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x434 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x60

    requires s0.stack[6] == 0x387

    requires s0.stack[13] == 0x60

    requires s0.stack[14] == 0x18b

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60;
      assert s1.Peek(6) == 0x387;
      assert s1.Peek(13) == 0x60;
      assert s1.Peek(14) == 0x18b;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0xf8;
      var s2 := Dup6(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0499);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s5, gas - 1)
      else
        ExecuteFromCFGNode_s132(s5, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 75
    * Starting at 0x43b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x60

    requires s0.stack[6] == 0x387

    requires s0.stack[13] == 0x60

    requires s0.stack[14] == 0x18b

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0445);
      assert s1.Peek(0) == 0x445;
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x387;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0575);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s5, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 100
    * Starting at 0x575
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x575 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x445

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x387

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x445;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x387;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0587);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s8, gas - 1)
      else
        ExecuteFromCFGNode_s134(s8, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 101
    * Starting at 0x580
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x580 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0587);
      assert s1.Peek(0) == 0x587;
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x387;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push2(s1, 0x05eb);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s3, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 115
    * Starting at 0x5eb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x587

    requires s0.stack[4] == 0x445

    requires s0.stack[9] == 0x60

    requires s0.stack[11] == 0x387

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x587;
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x387;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
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
      assert s11.Peek(2) == 0x587;
      assert s11.Peek(6) == 0x445;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(13) == 0x387;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0x18b;
      assert s11.Peek(23) == 0x60;
      assert s11.Peek(24) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 136
    * Segment Id for this node is: 102
    * Starting at 0x587
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x587 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x445

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x445;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x387;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Sub(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s5, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 76
    * Starting at 0x445
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x445 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x387

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x387;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0451);
      var s5 := Dup5(s4);
      var s6 := Dup8(s5);
      var s7 := Push2(s6, 0x05d7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s8, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 112
    * Starting at 0x5d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x451

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x387

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x451;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x387;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x05e6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s5, gas - 1)
      else
        ExecuteFromCFGNode_s139(s5, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 113
    * Starting at 0x5df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x451

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05e6);
      assert s1.Peek(0) == 0x5e6;
      assert s1.Peek(4) == 0x451;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x387;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push2(s1, 0x0601);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s3, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 116
    * Starting at 0x601
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x601 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x5e6

    requires s0.stack[4] == 0x451

    requires s0.stack[9] == 0x60

    requires s0.stack[11] == 0x387

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5e6;
      assert s1.Peek(4) == 0x451;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x387;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x12);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x5e6;
      assert s11.Peek(6) == 0x451;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(13) == 0x387;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0x18b;
      assert s11.Peek(23) == 0x60;
      assert s11.Peek(24) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 141
    * Segment Id for this node is: 114
    * Starting at 0x5e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x451

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x451;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x387;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Mod(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s5, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 77
    * Starting at 0x451
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x451 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x387

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x387;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Push2(s1, 0x045c);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x30);
      var s5 := Push2(s4, 0x052a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s6, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 91
    * Starting at 0x52a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x45c

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x387

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x45c;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x387;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x053d);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s146(s9, gas - 1)
      else
        ExecuteFromCFGNode_s144(s9, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 92
    * Starting at 0x536
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x45c

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x053d);
      assert s1.Peek(0) == 0x53d;
      assert s1.Peek(4) == 0x45c;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x387;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push2(s1, 0x05eb);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s3, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 115
    * Starting at 0x5eb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x53d

    requires s0.stack[4] == 0x45c

    requires s0.stack[9] == 0x60

    requires s0.stack[11] == 0x387

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x53d;
      assert s1.Peek(4) == 0x45c;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x387;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
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
      assert s11.Peek(2) == 0x53d;
      assert s11.Peek(6) == 0x45c;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(13) == 0x387;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0x18b;
      assert s11.Peek(23) == 0x60;
      assert s11.Peek(24) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 146
    * Segment Id for this node is: 93
    * Starting at 0x53d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x45c

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x45c;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x387;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s5, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 78
    * Starting at 0x45c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x387

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x387;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Push1(s1, 0xf8);
      var s3 := Shl(s2);
      var s4 := Dup2(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := Push2(s9, 0x0471);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s150(s11, gas - 1)
      else
        ExecuteFromCFGNode_s148(s11, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 79
    * Starting at 0x46a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x387

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0471);
      assert s1.Peek(0) == 0x471;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x387;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push2(s1, 0x0617);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s3, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 117
    * Starting at 0x617
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x617 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x471

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x471;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x387;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x471;
      assert s11.Peek(10) == 0x60;
      assert s11.Peek(12) == 0x387;
      assert s11.Peek(19) == 0x60;
      assert s11.Peek(20) == 0x18b;
      assert s11.Peek(22) == 0x60;
      assert s11.Peek(23) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 150
    * Segment Id for this node is: 80
    * Starting at 0x471
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x471 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x387

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x387;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xf8);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Not(s10);
      assert s11.Peek(7) == 0x60;
      assert s11.Peek(9) == 0x387;
      assert s11.Peek(16) == 0x60;
      assert s11.Peek(17) == 0x18b;
      assert s11.Peek(19) == 0x60;
      assert s11.Peek(20) == 0xf8;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push2(s19, 0x0492);
      var s21 := Dup5(s20);
      assert s21.Peek(1) == 0x492;
      assert s21.Peek(6) == 0x60;
      assert s21.Peek(8) == 0x387;
      assert s21.Peek(15) == 0x60;
      assert s21.Peek(16) == 0x18b;
      assert s21.Peek(18) == 0x60;
      assert s21.Peek(19) == 0xf8;
      var s22 := Dup8(s21);
      var s23 := Push2(s22, 0x0542);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s24, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 94
    * Starting at 0x542
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x542 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x492

    requires s0.stack[7] == 0x60

    requires s0.stack[9] == 0x387

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0x18b

    requires s0.stack[19] == 0x60

    requires s0.stack[20] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x492;
      assert s1.Peek(7) == 0x60;
      assert s1.Peek(9) == 0x387;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0x18b;
      assert s1.Peek(19) == 0x60;
      assert s1.Peek(20) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0551);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s154(s5, gas - 1)
      else
        ExecuteFromCFGNode_s152(s5, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 95
    * Starting at 0x54a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x492

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0551);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x492;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x387;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push2(s1, 0x0601);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s3, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 116
    * Starting at 0x601
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x601 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x551

    requires s0.stack[4] == 0x492

    requires s0.stack[9] == 0x60

    requires s0.stack[11] == 0x387

    requires s0.stack[18] == 0x60

    requires s0.stack[19] == 0x18b

    requires s0.stack[21] == 0x60

    requires s0.stack[22] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x551;
      assert s1.Peek(4) == 0x492;
      assert s1.Peek(9) == 0x60;
      assert s1.Peek(11) == 0x387;
      assert s1.Peek(18) == 0x60;
      assert s1.Peek(19) == 0x18b;
      assert s1.Peek(21) == 0x60;
      assert s1.Peek(22) == 0xf8;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x12);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x551;
      assert s11.Peek(6) == 0x492;
      assert s11.Peek(11) == 0x60;
      assert s11.Peek(13) == 0x387;
      assert s11.Peek(20) == 0x60;
      assert s11.Peek(21) == 0x18b;
      assert s11.Peek(23) == 0x60;
      assert s11.Peek(24) == 0xf8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 154
    * Segment Id for this node is: 96
    * Starting at 0x551
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x551 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x492

    requires s0.stack[8] == 0x60

    requires s0.stack[10] == 0x387

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0x18b

    requires s0.stack[20] == 0x60

    requires s0.stack[21] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x492;
      assert s1.Peek(8) == 0x60;
      assert s1.Peek(10) == 0x387;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0x18b;
      assert s1.Peek(20) == 0x60;
      assert s1.Peek(21) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s5, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 81
    * Starting at 0x492
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x60

    requires s0.stack[7] == 0x387

    requires s0.stack[14] == 0x60

    requires s0.stack[15] == 0x18b

    requires s0.stack[17] == 0x60

    requires s0.stack[18] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x60;
      assert s1.Peek(7) == 0x387;
      assert s1.Peek(14) == 0x60;
      assert s1.Peek(15) == 0x18b;
      assert s1.Peek(17) == 0x60;
      assert s1.Peek(18) == 0xf8;
      var s2 := Swap6(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0434);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s5, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 82
    * Starting at 0x499
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x499 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x60

    requires s0.stack[6] == 0x387

    requires s0.stack[13] == 0x60

    requires s0.stack[14] == 0x18b

    requires s0.stack[16] == 0x60

    requires s0.stack[17] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x60;
      assert s1.Peek(6) == 0x387;
      assert s1.Peek(13) == 0x60;
      assert s1.Peek(14) == 0x18b;
      assert s1.Peek(16) == 0x60;
      assert s1.Peek(17) == 0xf8;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s9, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 22
    * Starting at 0xc3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3 as nat
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
      var s5 := Push2(s4, 0x00cf);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s6, gas - 1)
      else
        ExecuteFromCFGNode_s158(s6, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 23
    * Starting at 0xcb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb as nat
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

  /** Node 159
    * Segment Id for this node is: 24
    * Starting at 0xcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x007a);
      var s4 := Push2(s3, 0x00de);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x04a2);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s8, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 83
    * Starting at 0x4a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xde

    requires s0.stack[3] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xde;
      assert s1.Peek(3) == 0x7a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x04b4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s162(s10, gas - 1)
      else
        ExecuteFromCFGNode_s161(s10, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 84
    * Starting at 0x4b0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xde

    requires s0.stack[4] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0xde;
      assert s1.Peek(5) == 0x7a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 162
    * Segment Id for this node is: 85
    * Starting at 0x4b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xde

    requires s0.stack[4] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde;
      assert s1.Peek(4) == 0x7a;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s7, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 25
    * Starting at 0xde
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7a;
      var s2 := Push1(s1, 0x06);
      var s3 := SStore(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s4, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 14
    * Starting at 0x7a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a as nat
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

  /** Node 165
    * Segment Id for this node is: 21
    * Starting at 0xbb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x007a);
      var s3 := Push2(s2, 0x0177);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s4, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 36
    * Starting at 0x177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x7a;
      var s2 := Push2(s1, 0x0175);
      var s3 := Push2(s2, 0x021a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s4, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 44
    * Starting at 0x21a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x175

    requires s0.stack[1] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x175;
      assert s1.Peek(1) == 0x7a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0229);
      var s4 := Push1(s3, 0x08);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0x09);
      var s7 := SLoad(s6);
      var s8 := Xor(s7);
      var s9 := Swap1(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s10, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 45
    * Starting at 0x229
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x229 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x175

    requires s0.stack[3] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x175;
      assert s1.Peek(3) == 0x7a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push2(s4, 0x023a);
      var s6 := Push1(s5, 0x07);
      var s7 := SLoad(s6);
      var s8 := Push1(s7, 0x08);
      var s9 := SLoad(s8);
      var s10 := Xor(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(0) == 0x23a;
      assert s11.Peek(4) == 0x175;
      assert s11.Peek(5) == 0x7a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s12, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 46
    * Starting at 0x23a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x175

    requires s0.stack[4] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x175;
      assert s1.Peek(4) == 0x7a;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x0e26d7a7);
      var s5 := Push1(s4, 0xe4);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Caller(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(7) == 0x175;
      assert s11.Peek(8) == 0x7a;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := Dup5(s18);
      var s20 := Dup2(s19);
      var s21 := And(s20);
      assert s21.Peek(6) == 0x175;
      assert s21.Peek(7) == 0x7a;
      var s22 := Push1(s21, 0x24);
      var s23 := Dup4(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x00);
      var s27 := Push1(s26, 0x44);
      var s28 := Dup4(s27);
      var s29 := Add(s28);
      var s30 := MStore(s29);
      var s31 := SelfBalance(s30);
      assert s31.Peek(6) == 0x175;
      assert s31.Peek(7) == 0x7a;
      var s32 := Push1(s31, 0x64);
      var s33 := Dup4(s32);
      var s34 := Add(s33);
      var s35 := MStore(s34);
      var s36 := Swap2(s35);
      var s37 := Swap3(s36);
      var s38 := Pop(s37);
      var s39 := Swap1(s38);
      var s40 := Dup3(s39);
      var s41 := And(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s170(s41, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 47
    * Starting at 0x271
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x271 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x175

    requires s0.stack[5] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(4) == 0x175;
      assert s1.Peek(5) == 0x7a;
      var s2 := Push4(s1, 0xe26d7a70);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x84);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup4(s9);
      var s11 := Sub(s10);
      assert s11.Peek(8) == 0x175;
      assert s11.Peek(9) == 0x7a;
      var s12 := Dup2(s11);
      var s13 := Push1(s12, 0x00);
      var s14 := Dup8(s13);
      var s15 := Dup1(s14);
      var s16 := ExtCodeSize(s15);
      var s17 := IsZero(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0294);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s21, gas - 1)
      else
        ExecuteFromCFGNode_s171(s21, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 48
    * Starting at 0x290
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x290 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[12] == 0x175

    requires s0.stack[13] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(13) == 0x175;
      assert s1.Peek(14) == 0x7a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 172
    * Segment Id for this node is: 49
    * Starting at 0x294
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x294 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[12] == 0x175

    requires s0.stack[13] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x175;
      assert s1.Peek(13) == 0x7a;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x02a8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s9, gas - 1)
      else
        ExecuteFromCFGNode_s173(s9, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 50
    * Starting at 0x29f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x175

    requires s0.stack[7] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x175;
      assert s1.Peek(8) == 0x7a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 174
    * Segment Id for this node is: 51
    * Starting at 0x2a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x175

    requires s0.stack[7] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x175;
      assert s1.Peek(7) == 0x7a;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(7) == 0x175;
      assert s11.Peek(8) == 0x7a;
      var s12 := And(s11);
      var s13 := Swap3(s12);
      var s14 := Pop(s13);
      var s15 := SelfBalance(s14);
      var s16 := Dup1(s15);
      var s17 := IsZero(s16);
      var s18 := Push2(s17, 0x08fc);
      var s19 := Mul(s18);
      var s20 := Swap3(s19);
      var s21 := Pop(s20);
      assert s21.Peek(6) == 0x175;
      assert s21.Peek(7) == 0x7a;
      var s22 := Swap1(s21);
      var s23 := Push1(s22, 0x00);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Dup2(s25);
      var s27 := Dup6(s26);
      var s28 := Dup9(s27);
      var s29 := Dup9(s28);
      var s30 := Call(s29);
      var s31 := Swap4(s30);
      assert s31.Peek(7) == 0x175;
      assert s31.Peek(8) == 0x7a;
      var s32 := Pop(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := IsZero(s35);
      var s37 := Dup1(s36);
      var s38 := IsZero(s37);
      var s39 := Push2(s38, 0x02e2);
      var s40 := JumpI(s39);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s39.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s40, gas - 1)
      else
        ExecuteFromCFGNode_s175(s40, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 52
    * Starting at 0x2d9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x175

    requires s0.stack[4] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x175;
      assert s1.Peek(5) == 0x7a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 176
    * Segment Id for this node is: 53
    * Starting at 0x2e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x175

    requires s0.stack[4] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x175;
      assert s1.Peek(4) == 0x7a;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s5, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 35
    * Starting at 0x175
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x175 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x7a;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s2, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 18
    * Starting at 0x9f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f as nat
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
      var s5 := Push2(s4, 0x00ab);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s180(s6, gas - 1)
      else
        ExecuteFromCFGNode_s179(s6, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 19
    * Starting at 0xa7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7 as nat
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

  /** Node 180
    * Segment Id for this node is: 20
    * Starting at 0xab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x007a);
      var s4 := Push1(s3, 0x04);
      var s5 := Dup1(s4);
      var s6 := SLoad(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := SStore(s10);
      assert s11.Peek(0) == 0x7a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s12, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 15
    * Starting at 0x7c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c as nat
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
      var s5 := Push2(s4, 0x0088);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s6, gas - 1)
      else
        ExecuteFromCFGNode_s182(s6, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 16
    * Starting at 0x84
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84 as nat
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

  /** Node 183
    * Segment Id for this node is: 17
    * Starting at 0x88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x007a);
      var s4 := PushN(s3, 13, 0x0b569c21f0fdbe9598d7140000);
      var s5 := Push1(s4, 0x06);
      var s6 := SStore(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s7, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 11
    * Starting at 0x65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65 as nat
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
      var s5 := Push2(s4, 0x0071);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s6, gas - 1)
      else
        ExecuteFromCFGNode_s185(s6, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 12
    * Starting at 0x6d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d as nat
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

  /** Node 186
    * Segment Id for this node is: 13
    * Starting at 0x71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x007a);
      var s4 := Push2(s3, 0x010e);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s5, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 31
    * Starting at 0x10e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x7a;
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
      assert s11.Peek(1) == 0x7a;
      var s12 := Push2(s11, 0x016d);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s190(s13, gas - 1)
      else
        ExecuteFromCFGNode_s188(s13, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 32
    * Starting at 0x121
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x7a;
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
      assert s11.Peek(3) == 0x7a;
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
      assert s21.Peek(4) == 0x7a;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s189(s25, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 33
    * Starting at 0x164
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x164 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7a;
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

  /** Node 190
    * Segment Id for this node is: 34
    * Starting at 0x16d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x7a;
      var s2 := Push2(s1, 0x0175);
      var s3 := Push2(s2, 0x0191);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s4, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 39
    * Starting at 0x191
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x175

    requires s0.stack[1] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x175;
      assert s1.Peek(1) == 0x7a;
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
      assert s11.Peek(1) == 0x175;
      assert s11.Peek(2) == 0x7a;
      var s12 := Push2(s11, 0x01eb);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s13, gas - 1)
      else
        ExecuteFromCFGNode_s192(s13, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 40
    * Starting at 0x1a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x175

    requires s0.stack[1] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x175;
      assert s1.Peek(2) == 0x7a;
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
      assert s11.Peek(3) == 0x175;
      assert s11.Peek(4) == 0x7a;
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
      assert s21.Peek(4) == 0x175;
      assert s21.Peek(5) == 0x7a;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x0164);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s27, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 33
    * Starting at 0x164
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x164 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x175

    requires s0.stack[2] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x175;
      assert s1.Peek(2) == 0x7a;
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
    * Segment Id for this node is: 41
    * Starting at 0x1eb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x175

    requires s0.stack[1] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x175;
      assert s1.Peek(1) == 0x7a;
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
      assert s11.Peek(4) == 0x175;
      assert s11.Peek(5) == 0x7a;
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
      assert s21.Peek(4) == 0x175;
      assert s21.Peek(5) == 0x7a;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := IsZero(s24);
      var s26 := Dup1(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0217);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s196(s29, gas - 1)
      else
        ExecuteFromCFGNode_s195(s29, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 42
    * Starting at 0x20e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x175

    requires s0.stack[2] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(2) == 0x175;
      assert s1.Peek(3) == 0x7a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 196
    * Segment Id for this node is: 43
    * Starting at 0x217
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x217 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x175

    requires s0.stack[2] == 0x7a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x175;
      assert s1.Peek(2) == 0x7a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s3, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 8
    * Starting at 0x59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x0060);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s4, gas - 1)
      else
        ExecuteFromCFGNode_s198(s4, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 9
    * Starting at 0x5f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f as nat
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

  /** Node 199
    * Segment Id for this node is: 10
    * Starting at 0x60
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60 as nat
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
