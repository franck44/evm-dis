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
      var s7 := Push2(s6, 0x0057);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s8, gas - 1)
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
      var s1 := Push0(s0);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shr(s3);
      var s5 := Dup1(s4);
      var s6 := Push4(s5, 0x2929abe6);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x0062);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s9, gas - 1)
      else
        ExecuteFromCFGNode_s2(s9, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x1d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x715018a6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0077);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s125(s5, gas - 1)
      else
        ExecuteFromCFGNode_s3(s5, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x28
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x008b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s122(s5, gas - 1)
      else
        ExecuteFromCFGNode_s4(s5, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x33
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xb29a8140);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00b5);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x3e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xd3335553);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00d4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x49
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00f3);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x54
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54 as nat
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

  /** Node 8
    * Segment Id for this node is: 28
    * Starting at 0xf3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf3 as nat
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
      var s5 := Push2(s4, 0x00fe);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s6, gas - 1)
      else
        ExecuteFromCFGNode_s9(s6, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 29
    * Starting at 0xfb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 10
    * Segment Id for this node is: 30
    * Starting at 0xfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0075);
      var s4 := Push2(s3, 0x010d);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0853);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s8, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 125
    * Starting at 0x853
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x853 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x10d

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10d;
      assert s1.Peek(3) == 0x75;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0863);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s13(s10, gas - 1)
      else
        ExecuteFromCFGNode_s12(s10, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 126
    * Starting at 0x860
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x860 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x10d

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x10d;
      assert s1.Peek(5) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 13
    * Segment Id for this node is: 127
    * Starting at 0x863
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x863 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x10d

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10d;
      assert s1.Peek(4) == 0x75;
      var s2 := Push2(s1, 0x086c);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x07f9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s5, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 115
    * Starting at 0x7f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x86c

    requires s0.stack[5] == 0x10d

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x86c;
      assert s1.Peek(5) == 0x10d;
      assert s1.Peek(6) == 0x75;
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
      assert s11.Peek(4) == 0x86c;
      assert s11.Peek(8) == 0x10d;
      assert s11.Peek(9) == 0x75;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x080f);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s14, gas - 1)
      else
        ExecuteFromCFGNode_s15(s14, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 116
    * Starting at 0x80c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x86c

    requires s0.stack[6] == 0x10d

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x86c;
      assert s1.Peek(7) == 0x10d;
      assert s1.Peek(8) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 16
    * Segment Id for this node is: 117
    * Starting at 0x80f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x86c

    requires s0.stack[6] == 0x10d

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x86c;
      assert s1.Peek(6) == 0x10d;
      assert s1.Peek(7) == 0x75;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s5, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 128
    * Starting at 0x86c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x10d

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10d;
      assert s1.Peek(5) == 0x75;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s7, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 31
    * Starting at 0x10d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x75;
      var s2 := Push2(s1, 0x027a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s3, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 59
    * Starting at 0x27a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x75;
      var s2 := Push2(s1, 0x0282);
      var s3 := Push2(s2, 0x040a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s4, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 71
    * Starting at 0x40a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x282

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x282;
      assert s1.Peek(2) == 0x75;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x282;
      assert s11.Peek(3) == 0x75;
      var s12 := Push2(s11, 0x0243);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s13, gas - 1)
      else
        ExecuteFromCFGNode_s21(s13, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 72
    * Starting at 0x41c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x282

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x282;
      assert s1.Peek(3) == 0x75;
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
      assert s11.Peek(3) == 0x282;
      assert s11.Peek(5) == 0x75;
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
      assert s21.Peek(4) == 0x282;
      assert s21.Peek(6) == 0x75;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x0151);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s27, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x282

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x282;
      assert s1.Peek(3) == 0x75;
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

  /** Node 23
    * Segment Id for this node is: 52
    * Starting at 0x243
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x282

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x282;
      assert s1.Peek(2) == 0x75;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s2, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 60
    * Starting at 0x282
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x282 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x75;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x02e7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s10, gas - 1)
      else
        ExecuteFromCFGNode_s25(s10, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 61
    * Starting at 0x291
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x291 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x75;
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
      assert s11.Peek(4) == 0x75;
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
      assert s21.Peek(4) == 0x75;
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
      assert s31.Peek(2) == 0x75;
      var s32 := Push2(s31, 0x0151);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s33, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x75;
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
    * Segment Id for this node is: 62
    * Starting at 0x2e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x75;
      var s2 := Push2(s1, 0x0277);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0463);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s5, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 73
    * Starting at 0x463
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x277

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x277;
      assert s1.Peek(3) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup4(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x277;
      assert s11.Peek(8) == 0x75;
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
      assert s21.Peek(7) == 0x277;
      assert s21.Peek(9) == 0x75;
      var s22 := Or(s21);
      var s23 := Dup5(s22);
      var s24 := SStore(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Swap2(s26);
      var s28 := Swap1(s27);
      var s29 := Swap3(s28);
      var s30 := And(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(5) == 0x277;
      assert s31.Peek(7) == 0x75;
      var s32 := Dup4(s31);
      var s33 := Swap2(s32);
      var s34 := Push32(s33, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s35 := Swap2(s34);
      var s36 := Swap1(s35);
      var s37 := Log3(s36);
      var s38 := Pop(s37);
      var s39 := Pop(s38);
      var s40 := Jump(s39);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s40, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 58
    * Starting at 0x277
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x277 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x75;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s3, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 13
    * Starting at 0x75
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75 as nat
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

  /** Node 31
    * Segment Id for this node is: 24
    * Starting at 0xd4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4 as nat
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
      var s5 := Push2(s4, 0x00df);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s6, gas - 1)
      else
        ExecuteFromCFGNode_s32(s6, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 25
    * Starting at 0xdc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 33
    * Segment Id for this node is: 26
    * Starting at 0xdf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0075);
      var s4 := Push2(s3, 0x00ee);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x083c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s8, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 122
    * Starting at 0x83c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xee

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xee;
      assert s1.Peek(3) == 0x75;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x084c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s10, gas - 1)
      else
        ExecuteFromCFGNode_s35(s10, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 123
    * Starting at 0x849
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x849 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xee

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0xee;
      assert s1.Peek(5) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 36
    * Segment Id for this node is: 124
    * Starting at 0x84c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xee

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee;
      assert s1.Peek(4) == 0x75;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s7, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 27
    * Starting at 0xee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x75;
      var s2 := Push2(s1, 0x0265);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s3, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 56
    * Starting at 0x265
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x265 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x75;
      var s2 := Push2(s1, 0x026d);
      var s3 := Push2(s2, 0x040a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s4, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 71
    * Starting at 0x40a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x26d

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x26d;
      assert s1.Peek(2) == 0x75;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x26d;
      assert s11.Peek(3) == 0x75;
      var s12 := Push2(s11, 0x0243);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s13, gas - 1)
      else
        ExecuteFromCFGNode_s40(s13, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 72
    * Starting at 0x41c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x26d

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x26d;
      assert s1.Peek(3) == 0x75;
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
      assert s11.Peek(3) == 0x26d;
      assert s11.Peek(5) == 0x75;
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
      assert s21.Peek(4) == 0x26d;
      assert s21.Peek(6) == 0x75;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x0151);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s27, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x26d

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x26d;
      assert s1.Peek(3) == 0x75;
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

  /** Node 42
    * Segment Id for this node is: 52
    * Starting at 0x243
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x26d

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x26d;
      assert s1.Peek(2) == 0x75;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s2, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 57
    * Starting at 0x26d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x75;
      var s2 := Push2(s1, 0x0277);
      var s3 := Dup2(s2);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x01a7);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s6, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 42
    * Starting at 0x1a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x277

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x277;
      assert s1.Peek(4) == 0x75;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Swap1(s7);
      var s9 := Push2(s8, 0x02f0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s10, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 63
    * Starting at 0x2f0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x277

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x277;
      assert s1.Peek(4) == 0x75;
      var s2 := Dup1(s1);
      var s3 := SelfBalance(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0340);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s7, gas - 1)
      else
        ExecuteFromCFGNode_s46(s7, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 64
    * Starting at 0x2f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x277

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x277;
      assert s1.Peek(5) == 0x75;
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
      assert s11.Peek(5) == 0x277;
      assert s11.Peek(7) == 0x75;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a20696e73756666696369656e742062616c616e6365000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x277;
      assert s21.Peek(7) == 0x75;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x0151);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s26, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x277

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x277;
      assert s1.Peek(5) == 0x75;
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
    * Segment Id for this node is: 65
    * Starting at 0x340
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x277

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x277;
      assert s1.Peek(4) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Dup3(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(6) == 0x277;
      assert s11.Peek(8) == 0x75;
      var s12 := MLoad(s11);
      var s13 := Push0(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := MLoad(s14);
      var s16 := Dup1(s15);
      var s17 := Dup4(s16);
      var s18 := Sub(s17);
      var s19 := Dup2(s18);
      var s20 := Dup6(s19);
      var s21 := Dup8(s20);
      assert s21.Peek(12) == 0x277;
      assert s21.Peek(14) == 0x75;
      var s22 := Gas(s21);
      var s23 := Call(s22);
      var s24 := Swap3(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := ReturnDataSize(s27);
      var s29 := Dup1(s28);
      var s30 := Push0(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(8) == 0x277;
      assert s31.Peek(10) == 0x75;
      var s32 := Eq(s31);
      var s33 := Push2(s32, 0x0389);
      var s34 := JumpI(s33);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s33.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s34, gas - 1)
      else
        ExecuteFromCFGNode_s49(s34, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 66
    * Starting at 0x369
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x369 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x277

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(7) == 0x277;
      assert s1.Peek(9) == 0x75;
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
      assert s11.Peek(8) == 0x277;
      assert s11.Peek(10) == 0x75;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push0(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(10) == 0x277;
      assert s21.Peek(12) == 0x75;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x038e);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s25, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 68
    * Starting at 0x38e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x277

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x277;
      assert s1.Peek(8) == 0x75;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Dup1(s5);
      var s7 := Push2(s6, 0x0405);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s8, gas - 1)
      else
        ExecuteFromCFGNode_s51(s8, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 69
    * Starting at 0x398
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x398 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x277

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x277;
      assert s1.Peek(6) == 0x75;
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
      assert s11.Peek(6) == 0x277;
      assert s11.Peek(8) == 0x75;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x3a);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a20756e61626c6520746f2073656e642076616c75652c2072);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x277;
      assert s21.Peek(8) == 0x75;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6563697069656e74206d61792068617665207265766572746564000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0151);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s31, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x277

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x277;
      assert s1.Peek(6) == 0x75;
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

  /** Node 53
    * Segment Id for this node is: 70
    * Starting at 0x405
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x405 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x277

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x277;
      assert s1.Peek(5) == 0x75;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s5, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 67
    * Starting at 0x389
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x389 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x277

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x277;
      assert s1.Peek(8) == 0x75;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s50(s4, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 20
    * Starting at 0xb5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5 as nat
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
      var s5 := Push2(s4, 0x00c0);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s6, gas - 1)
      else
        ExecuteFromCFGNode_s56(s6, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 21
    * Starting at 0xbd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 57
    * Segment Id for this node is: 22
    * Starting at 0xc0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0075);
      var s4 := Push2(s3, 0x00cf);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0814);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s8, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 118
    * Starting at 0x814
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x814 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xcf

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcf;
      assert s1.Peek(3) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0825);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s11, gas - 1)
      else
        ExecuteFromCFGNode_s59(s11, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 119
    * Starting at 0x822
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x822 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xcf

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0xcf;
      assert s1.Peek(6) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 60
    * Segment Id for this node is: 120
    * Starting at 0x825
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x825 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xcf

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xcf;
      assert s1.Peek(5) == 0x75;
      var s2 := Push2(s1, 0x082e);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x07f9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s5, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 115
    * Starting at 0x7f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x82e

    requires s0.stack[6] == 0xcf

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x82e;
      assert s1.Peek(6) == 0xcf;
      assert s1.Peek(7) == 0x75;
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
      assert s11.Peek(4) == 0x82e;
      assert s11.Peek(9) == 0xcf;
      assert s11.Peek(10) == 0x75;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x080f);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s14, gas - 1)
      else
        ExecuteFromCFGNode_s62(s14, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 116
    * Starting at 0x80c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x82e

    requires s0.stack[7] == 0xcf

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x82e;
      assert s1.Peek(8) == 0xcf;
      assert s1.Peek(9) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 63
    * Segment Id for this node is: 117
    * Starting at 0x80f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x82e

    requires s0.stack[7] == 0xcf

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x82e;
      assert s1.Peek(7) == 0xcf;
      assert s1.Peek(8) == 0x75;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s5, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 121
    * Starting at 0x82e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xcf

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xcf;
      assert s1.Peek(6) == 0x75;
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
      assert s11.Peek(1) == 0xcf;
      assert s11.Peek(4) == 0x75;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s13, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 23
    * Starting at 0xcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x75;
      var s2 := Push2(s1, 0x0245);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s3, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 53
    * Starting at 0x245
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x245 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x75;
      var s2 := Push2(s1, 0x024d);
      var s3 := Push2(s2, 0x040a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s4, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 71
    * Starting at 0x40a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x24d

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x24d;
      assert s1.Peek(3) == 0x75;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x24d;
      assert s11.Peek(4) == 0x75;
      var s12 := Push2(s11, 0x0243);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s13, gas - 1)
      else
        ExecuteFromCFGNode_s68(s13, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 72
    * Starting at 0x41c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x24d

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x24d;
      assert s1.Peek(4) == 0x75;
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
      assert s11.Peek(3) == 0x24d;
      assert s11.Peek(6) == 0x75;
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
      assert s21.Peek(4) == 0x24d;
      assert s21.Peek(7) == 0x75;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x0151);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s27, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x24d

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x24d;
      assert s1.Peek(4) == 0x75;
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

  /** Node 70
    * Segment Id for this node is: 52
    * Starting at 0x243
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x24d

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x24d;
      assert s1.Peek(3) == 0x75;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s2, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 54
    * Starting at 0x24d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x75;
      var s2 := Push2(s1, 0x0261);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup4(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(3) == 0x261;
      assert s11.Peek(6) == 0x75;
      var s12 := Push2(s11, 0x04b2);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s13, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 74
    * Starting at 0x4b2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x261

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x261;
      assert s1.Peek(6) == 0x75;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup5(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x261;
      assert s11.Peek(11) == 0x75;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup1(s17);
      var s19 := Dup4(s18);
      var s20 := Add(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(9) == 0x261;
      assert s21.Peek(12) == 0x75;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Dup4(s23);
      var s25 := MLoad(s24);
      var s26 := Dup1(s25);
      var s27 := Dup5(s26);
      var s28 := Sub(s27);
      var s29 := Swap1(s28);
      var s30 := Swap2(s29);
      var s31 := Add(s30);
      assert s31.Peek(8) == 0x261;
      assert s31.Peek(11) == 0x75;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x64);
      var s35 := Swap1(s34);
      var s36 := Swap3(s35);
      var s37 := Add(s36);
      var s38 := Dup4(s37);
      var s39 := MStore(s38);
      var s40 := Push1(s39, 0x20);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s73(s41, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 75
    * Starting at 0x4e3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x261

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x261;
      assert s1.Peek(12) == 0x75;
      var s2 := Add(s1);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xe0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Push4(s10, 0xa9059cbb);
      assert s11.Peek(10) == 0x261;
      assert s11.Peek(13) == 0x75;
      var s12 := Push1(s11, 0xe0);
      var s13 := Shl(s12);
      var s14 := Or(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Dup4(s16);
      var s18 := MLoad(s17);
      var s19 := Dup1(s18);
      var s20 := Dup6(s19);
      var s21 := Add(s20);
      assert s21.Peek(9) == 0x261;
      assert s21.Peek(12) == 0x75;
      var s22 := Swap1(s21);
      var s23 := Swap5(s22);
      var s24 := MStore(s23);
      var s25 := Dup1(s24);
      var s26 := Dup5(s25);
      var s27 := MStore(s26);
      var s28 := Push32(s27, 0x5361666545524332303a206c6f772d6c6576656c2063616c6c206661696c6564);
      var s29 := Swap1(s28);
      var s30 := Dup5(s29);
      var s31 := Add(s30);
      assert s31.Peek(8) == 0x261;
      assert s31.Peek(11) == 0x75;
      var s32 := MStore(s31);
      var s33 := Push2(s32, 0x0405);
      var s34 := Swap3(s33);
      var s35 := Dup7(s34);
      var s36 := Swap3(s35);
      var s37 := Swap2(s36);
      var s38 := Push0(s37);
      var s39 := Swap2(s38);
      var s40 := Push2(s39, 0x0541);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s74(s41, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 76
    * Starting at 0x538
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x538 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x541

    requires s0.stack[6] == 0x405

    requires s0.stack[10] == 0x261

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(3) == 0x541;
      assert s1.Peek(7) == 0x405;
      assert s1.Peek(11) == 0x261;
      assert s1.Peek(14) == 0x75;
      var s2 := And(s1);
      var s3 := Swap1(s2);
      var s4 := Dup5(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x05c0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s7, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 81
    * Starting at 0x5c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x541

    requires s0.stack[7] == 0x405

    requires s0.stack[11] == 0x261

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x541;
      assert s1.Peek(7) == 0x405;
      assert s1.Peek(11) == 0x261;
      assert s1.Peek(14) == 0x75;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x05ce);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Push0(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x05d6);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s9, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 83
    * Starting at 0x5d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0x5ce

    requires s0.stack[9] == 0x541

    requires s0.stack[13] == 0x405

    requires s0.stack[17] == 0x261

    requires s0.stack[20] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5ce;
      assert s1.Peek(9) == 0x541;
      assert s1.Peek(13) == 0x405;
      assert s1.Peek(17) == 0x261;
      assert s1.Peek(20) == 0x75;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := SelfBalance(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0637);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s8, gas - 1)
      else
        ExecuteFromCFGNode_s77(s8, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 84
    * Starting at 0x5e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0x5ce

    requires s0.stack[10] == 0x541

    requires s0.stack[14] == 0x405

    requires s0.stack[18] == 0x261

    requires s0.stack[21] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x5ce;
      assert s1.Peek(11) == 0x541;
      assert s1.Peek(15) == 0x405;
      assert s1.Peek(19) == 0x261;
      assert s1.Peek(22) == 0x75;
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
      assert s11.Peek(8) == 0x5ce;
      assert s11.Peek(13) == 0x541;
      assert s11.Peek(17) == 0x405;
      assert s11.Peek(21) == 0x261;
      assert s11.Peek(24) == 0x75;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a20696e73756666696369656e742062616c616e636520666f);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(8) == 0x5ce;
      assert s21.Peek(13) == 0x541;
      assert s21.Peek(17) == 0x405;
      assert s21.Peek(21) == 0x261;
      assert s21.Peek(24) == 0x75;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x1c8818d85b1b);
      var s24 := Push1(s23, 0xd2);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(6) == 0x5ce;
      assert s31.Peek(11) == 0x541;
      assert s31.Peek(15) == 0x405;
      assert s31.Peek(19) == 0x261;
      assert s31.Peek(22) == 0x75;
      var s32 := Push2(s31, 0x0151);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s33, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[6] == 0x5ce

    requires s0.stack[11] == 0x541

    requires s0.stack[15] == 0x405

    requires s0.stack[19] == 0x261

    requires s0.stack[22] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x5ce;
      assert s1.Peek(11) == 0x541;
      assert s1.Peek(15) == 0x405;
      assert s1.Peek(19) == 0x261;
      assert s1.Peek(22) == 0x75;
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

  /** Node 79
    * Segment Id for this node is: 85
    * Starting at 0x637
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x637 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0x5ce

    requires s0.stack[10] == 0x541

    requires s0.stack[14] == 0x405

    requires s0.stack[18] == 0x261

    requires s0.stack[21] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x5ce;
      assert s1.Peek(10) == 0x541;
      assert s1.Peek(14) == 0x405;
      assert s1.Peek(18) == 0x261;
      assert s1.Peek(21) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup7(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(9) == 0x5ce;
      assert s11.Peek(14) == 0x541;
      assert s11.Peek(18) == 0x405;
      assert s11.Peek(22) == 0x261;
      assert s11.Peek(25) == 0x75;
      var s12 := Dup8(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0652);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x08ed);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s19, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 141
    * Starting at 0x8ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[2] == 0x652

    requires s0.stack[12] == 0x5ce

    requires s0.stack[17] == 0x541

    requires s0.stack[21] == 0x405

    requires s0.stack[25] == 0x261

    requires s0.stack[28] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x652;
      assert s1.Peek(12) == 0x5ce;
      assert s1.Peek(17) == 0x541;
      assert s1.Peek(21) == 0x405;
      assert s1.Peek(25) == 0x261;
      assert s1.Peek(28) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push2(s4, 0x08fe);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x08cb);
      assert s11.Peek(0) == 0x8cb;
      assert s11.Peek(4) == 0x8fe;
      assert s11.Peek(9) == 0x652;
      assert s11.Peek(19) == 0x5ce;
      assert s11.Peek(24) == 0x541;
      assert s11.Peek(28) == 0x405;
      assert s11.Peek(32) == 0x261;
      assert s11.Peek(35) == 0x75;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s12, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 137
    * Starting at 0x8cb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 36

    requires s0.stack[3] == 0x8fe

    requires s0.stack[8] == 0x652

    requires s0.stack[18] == 0x5ce

    requires s0.stack[23] == 0x541

    requires s0.stack[27] == 0x405

    requires s0.stack[31] == 0x261

    requires s0.stack[34] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8fe;
      assert s1.Peek(8) == 0x652;
      assert s1.Peek(18) == 0x5ce;
      assert s1.Peek(23) == 0x541;
      assert s1.Peek(27) == 0x405;
      assert s1.Peek(31) == 0x261;
      assert s1.Peek(34) == 0x75;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s82(s2, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 138
    * Starting at 0x8cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[4] == 0x8fe

    requires s0.stack[9] == 0x652

    requires s0.stack[19] == 0x5ce

    requires s0.stack[24] == 0x541

    requires s0.stack[28] == 0x405

    requires s0.stack[32] == 0x261

    requires s0.stack[35] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x8fe;
      assert s1.Peek(9) == 0x652;
      assert s1.Peek(19) == 0x5ce;
      assert s1.Peek(24) == 0x541;
      assert s1.Peek(28) == 0x405;
      assert s1.Peek(32) == 0x261;
      assert s1.Peek(35) == 0x75;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x08e5);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s7, gas - 1)
      else
        ExecuteFromCFGNode_s83(s7, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 139
    * Starting at 0x8d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[4] == 0x8fe

    requires s0.stack[9] == 0x652

    requires s0.stack[19] == 0x5ce

    requires s0.stack[24] == 0x541

    requires s0.stack[28] == 0x405

    requires s0.stack[32] == 0x261

    requires s0.stack[35] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x8fe;
      assert s1.Peek(10) == 0x652;
      assert s1.Peek(20) == 0x5ce;
      assert s1.Peek(25) == 0x541;
      assert s1.Peek(29) == 0x405;
      assert s1.Peek(33) == 0x261;
      assert s1.Peek(36) == 0x75;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x08cd);
      assert s11.Peek(0) == 0x8cd;
      assert s11.Peek(5) == 0x8fe;
      assert s11.Peek(10) == 0x652;
      assert s11.Peek(20) == 0x5ce;
      assert s11.Peek(25) == 0x541;
      assert s11.Peek(29) == 0x405;
      assert s11.Peek(33) == 0x261;
      assert s11.Peek(36) == 0x75;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s12, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 140
    * Starting at 0x8e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[4] == 0x8fe

    requires s0.stack[9] == 0x652

    requires s0.stack[19] == 0x5ce

    requires s0.stack[24] == 0x541

    requires s0.stack[28] == 0x405

    requires s0.stack[32] == 0x261

    requires s0.stack[35] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x8fe;
      assert s1.Peek(9) == 0x652;
      assert s1.Peek(19) == 0x5ce;
      assert s1.Peek(24) == 0x541;
      assert s1.Peek(28) == 0x405;
      assert s1.Peek(32) == 0x261;
      assert s1.Peek(35) == 0x75;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push0(s3);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s8, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 142
    * Starting at 0x8fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[4] == 0x652

    requires s0.stack[14] == 0x5ce

    requires s0.stack[19] == 0x541

    requires s0.stack[23] == 0x405

    requires s0.stack[27] == 0x261

    requires s0.stack[30] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x652;
      assert s1.Peek(14) == 0x5ce;
      assert s1.Peek(19) == 0x541;
      assert s1.Peek(23) == 0x405;
      assert s1.Peek(27) == 0x261;
      assert s1.Peek(30) == 0x75;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s10, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 86
    * Starting at 0x652
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x652 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[10] == 0x5ce

    requires s0.stack[15] == 0x541

    requires s0.stack[19] == 0x405

    requires s0.stack[23] == 0x261

    requires s0.stack[26] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x5ce;
      assert s1.Peek(15) == 0x541;
      assert s1.Peek(19) == 0x405;
      assert s1.Peek(23) == 0x261;
      assert s1.Peek(26) == 0x75;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup6(s8);
      var s10 := Dup8(s9);
      var s11 := Gas(s10);
      assert s11.Peek(17) == 0x5ce;
      assert s11.Peek(22) == 0x541;
      assert s11.Peek(26) == 0x405;
      assert s11.Peek(30) == 0x261;
      assert s11.Peek(33) == 0x75;
      var s12 := Call(s11);
      var s13 := Swap3(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := ReturnDataSize(s16);
      var s18 := Dup1(s17);
      var s19 := Push0(s18);
      var s20 := Dup2(s19);
      var s21 := Eq(s20);
      assert s21.Peek(11) == 0x5ce;
      assert s21.Peek(16) == 0x541;
      assert s21.Peek(20) == 0x405;
      assert s21.Peek(24) == 0x261;
      assert s21.Peek(27) == 0x75;
      var s22 := Push2(s21, 0x068c);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s23, gas - 1)
      else
        ExecuteFromCFGNode_s87(s23, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 87
    * Starting at 0x66c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[10] == 0x5ce

    requires s0.stack[15] == 0x541

    requires s0.stack[19] == 0x405

    requires s0.stack[23] == 0x261

    requires s0.stack[26] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(11) == 0x5ce;
      assert s1.Peek(16) == 0x541;
      assert s1.Peek(20) == 0x405;
      assert s1.Peek(24) == 0x261;
      assert s1.Peek(27) == 0x75;
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
      assert s11.Peek(12) == 0x5ce;
      assert s11.Peek(17) == 0x541;
      assert s11.Peek(21) == 0x405;
      assert s11.Peek(25) == 0x261;
      assert s11.Peek(28) == 0x75;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push0(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(14) == 0x5ce;
      assert s21.Peek(19) == 0x541;
      assert s21.Peek(23) == 0x405;
      assert s21.Peek(27) == 0x261;
      assert s21.Peek(30) == 0x75;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x0691);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s25, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 89
    * Starting at 0x691
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x691 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[10] == 0x5ce

    requires s0.stack[15] == 0x541

    requires s0.stack[19] == 0x405

    requires s0.stack[23] == 0x261

    requires s0.stack[26] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x5ce;
      assert s1.Peek(15) == 0x541;
      assert s1.Peek(19) == 0x405;
      assert s1.Peek(23) == 0x261;
      assert s1.Peek(26) == 0x75;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x06a2);
      var s8 := Dup8(s7);
      var s9 := Dup4(s8);
      var s10 := Dup4(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(4) == 0x6a2;
      assert s11.Peek(12) == 0x5ce;
      assert s11.Peek(17) == 0x541;
      assert s11.Peek(21) == 0x405;
      assert s11.Peek(25) == 0x261;
      assert s11.Peek(28) == 0x75;
      var s12 := Push2(s11, 0x06ad);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s13, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 91
    * Starting at 0x6ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[4] == 0x6a2

    requires s0.stack[12] == 0x5ce

    requires s0.stack[17] == 0x541

    requires s0.stack[21] == 0x405

    requires s0.stack[25] == 0x261

    requires s0.stack[28] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6a2;
      assert s1.Peek(12) == 0x5ce;
      assert s1.Peek(17) == 0x541;
      assert s1.Peek(21) == 0x405;
      assert s1.Peek(25) == 0x261;
      assert s1.Peek(28) == 0x75;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x071b);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s6, gas - 1)
      else
        ExecuteFromCFGNode_s90(s6, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 92
    * Starting at 0x6b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0x6a2

    requires s0.stack[13] == 0x5ce

    requires s0.stack[18] == 0x541

    requires s0.stack[22] == 0x405

    requires s0.stack[26] == 0x261

    requires s0.stack[29] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(6) == 0x6a2;
      assert s1.Peek(14) == 0x5ce;
      assert s1.Peek(19) == 0x541;
      assert s1.Peek(23) == 0x405;
      assert s1.Peek(27) == 0x261;
      assert s1.Peek(30) == 0x75;
      var s2 := MLoad(s1);
      var s3 := Push0(s2);
      var s4 := Sub(s3);
      var s5 := Push2(s4, 0x0714);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s6, gas - 1)
      else
        ExecuteFromCFGNode_s91(s6, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 93
    * Starting at 0x6be
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0x6a2

    requires s0.stack[13] == 0x5ce

    requires s0.stack[18] == 0x541

    requires s0.stack[22] == 0x405

    requires s0.stack[26] == 0x261

    requires s0.stack[29] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(6) == 0x6a2;
      assert s1.Peek(14) == 0x5ce;
      assert s1.Peek(19) == 0x541;
      assert s1.Peek(23) == 0x405;
      assert s1.Peek(27) == 0x261;
      assert s1.Peek(30) == 0x75;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup6(s5);
      var s7 := And(s6);
      var s8 := ExtCodeSize(s7);
      var s9 := Push2(s8, 0x0714);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s10, gas - 1)
      else
        ExecuteFromCFGNode_s92(s10, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 94
    * Starting at 0x6cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0x6a2

    requires s0.stack[13] == 0x5ce

    requires s0.stack[18] == 0x541

    requires s0.stack[22] == 0x405

    requires s0.stack[26] == 0x261

    requires s0.stack[29] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x6a2;
      assert s1.Peek(14) == 0x5ce;
      assert s1.Peek(19) == 0x541;
      assert s1.Peek(23) == 0x405;
      assert s1.Peek(27) == 0x261;
      assert s1.Peek(30) == 0x75;
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
      assert s11.Peek(8) == 0x6a2;
      assert s11.Peek(16) == 0x5ce;
      assert s11.Peek(21) == 0x541;
      assert s11.Peek(25) == 0x405;
      assert s11.Peek(29) == 0x261;
      assert s11.Peek(32) == 0x75;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a2063616c6c20746f206e6f6e2d636f6e7472616374000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(8) == 0x6a2;
      assert s21.Peek(16) == 0x5ce;
      assert s21.Peek(21) == 0x541;
      assert s21.Peek(25) == 0x405;
      assert s21.Peek(29) == 0x261;
      assert s21.Peek(32) == 0x75;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x0151);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s26, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[6] == 0x6a2

    requires s0.stack[14] == 0x5ce

    requires s0.stack[19] == 0x541

    requires s0.stack[23] == 0x405

    requires s0.stack[27] == 0x261

    requires s0.stack[30] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x6a2;
      assert s1.Peek(14) == 0x5ce;
      assert s1.Peek(19) == 0x541;
      assert s1.Peek(23) == 0x405;
      assert s1.Peek(27) == 0x261;
      assert s1.Peek(30) == 0x75;
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

  /** Node 94
    * Segment Id for this node is: 95
    * Starting at 0x714
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x714 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0x6a2

    requires s0.stack[13] == 0x5ce

    requires s0.stack[18] == 0x541

    requires s0.stack[22] == 0x405

    requires s0.stack[26] == 0x261

    requires s0.stack[29] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x6a2;
      assert s1.Peek(13) == 0x5ce;
      assert s1.Peek(18) == 0x541;
      assert s1.Peek(22) == 0x405;
      assert s1.Peek(26) == 0x261;
      assert s1.Peek(29) == 0x75;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x05ce);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s5, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 82
    * Starting at 0x5ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0x6a2

    requires s0.stack[13] == 0x5ce

    requires s0.stack[18] == 0x541

    requires s0.stack[22] == 0x405

    requires s0.stack[26] == 0x261

    requires s0.stack[29] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x6a2;
      assert s1.Peek(13) == 0x5ce;
      assert s1.Peek(18) == 0x541;
      assert s1.Peek(22) == 0x405;
      assert s1.Peek(26) == 0x261;
      assert s1.Peek(29) == 0x75;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s8, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 90
    * Starting at 0x6a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[8] == 0x5ce

    requires s0.stack[13] == 0x541

    requires s0.stack[17] == 0x405

    requires s0.stack[21] == 0x261

    requires s0.stack[24] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x5ce;
      assert s1.Peek(13) == 0x541;
      assert s1.Peek(17) == 0x405;
      assert s1.Peek(21) == 0x261;
      assert s1.Peek(24) == 0x75;
      var s2 := Swap(s1, 8);
      var s3 := Swap7(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s11, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 82
    * Starting at 0x5ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x541

    requires s0.stack[9] == 0x405

    requires s0.stack[13] == 0x261

    requires s0.stack[16] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x541;
      assert s1.Peek(9) == 0x405;
      assert s1.Peek(13) == 0x261;
      assert s1.Peek(16) == 0x75;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s8, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 77
    * Starting at 0x541
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x405

    requires s0.stack[8] == 0x261

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x405;
      assert s1.Peek(8) == 0x261;
      assert s1.Peek(11) == 0x75;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := MLoad(s4);
      var s6 := Push0(s5);
      var s7 := Eq(s6);
      var s8 := Dup1(s7);
      var s9 := Push2(s8, 0x0561);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s10, gas - 1)
      else
        ExecuteFromCFGNode_s99(s10, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 78
    * Starting at 0x54d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x405

    requires s0.stack[8] == 0x261

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x405;
      assert s1.Peek(7) == 0x261;
      assert s1.Peek(10) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := MLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x0561);
      assert s11.Peek(0) == 0x561;
      assert s11.Peek(6) == 0x405;
      assert s11.Peek(10) == 0x261;
      assert s11.Peek(13) == 0x75;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x08ac);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s15, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 133
    * Starting at 0x8ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x561

    requires s0.stack[6] == 0x405

    requires s0.stack[10] == 0x261

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x561;
      assert s1.Peek(6) == 0x405;
      assert s1.Peek(10) == 0x261;
      assert s1.Peek(13) == 0x75;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x08bc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s10, gas - 1)
      else
        ExecuteFromCFGNode_s101(s10, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 134
    * Starting at 0x8b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x561

    requires s0.stack[7] == 0x405

    requires s0.stack[11] == 0x261

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x561;
      assert s1.Peek(8) == 0x405;
      assert s1.Peek(12) == 0x261;
      assert s1.Peek(15) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 102
    * Segment Id for this node is: 135
    * Starting at 0x8bc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x561

    requires s0.stack[7] == 0x405

    requires s0.stack[11] == 0x261

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x561;
      assert s1.Peek(7) == 0x405;
      assert s1.Peek(11) == 0x261;
      assert s1.Peek(14) == 0x75;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x086c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s104(s10, gas - 1)
      else
        ExecuteFromCFGNode_s103(s10, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 136
    * Starting at 0x8c8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x561

    requires s0.stack[8] == 0x405

    requires s0.stack[12] == 0x261

    requires s0.stack[15] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x561;
      assert s1.Peek(9) == 0x405;
      assert s1.Peek(13) == 0x261;
      assert s1.Peek(16) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 104
    * Segment Id for this node is: 128
    * Starting at 0x86c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x561

    requires s0.stack[8] == 0x405

    requires s0.stack[12] == 0x261

    requires s0.stack[15] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x561;
      assert s1.Peek(8) == 0x405;
      assert s1.Peek(12) == 0x261;
      assert s1.Peek(15) == 0x75;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s7, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 79
    * Starting at 0x561
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x561 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x405

    requires s0.stack[8] == 0x261

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x405;
      assert s1.Peek(8) == 0x261;
      assert s1.Peek(11) == 0x75;
      var s2 := Push2(s1, 0x0405);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s3, gas - 1)
      else
        ExecuteFromCFGNode_s106(s3, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 80
    * Starting at 0x566
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x566 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x405

    requires s0.stack[7] == 0x261

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x405;
      assert s1.Peek(8) == 0x261;
      assert s1.Peek(11) == 0x75;
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
      assert s11.Peek(6) == 0x405;
      assert s11.Peek(10) == 0x261;
      assert s11.Peek(13) == 0x75;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x2a);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x5361666545524332303a204552433230206f7065726174696f6e20646964206e);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x405;
      assert s21.Peek(10) == 0x261;
      assert s21.Peek(13) == 0x75;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 10, 0x1bdd081cdd58d8d95959);
      var s24 := Push1(s23, 0xb2);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x405;
      assert s31.Peek(8) == 0x261;
      assert s31.Peek(11) == 0x75;
      var s32 := Push2(s31, 0x0151);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s33, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x405

    requires s0.stack[8] == 0x261

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x405;
      assert s1.Peek(8) == 0x261;
      assert s1.Peek(11) == 0x75;
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

  /** Node 108
    * Segment Id for this node is: 70
    * Starting at 0x405
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x405 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x405

    requires s0.stack[7] == 0x261

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x405;
      assert s1.Peek(7) == 0x261;
      assert s1.Peek(10) == 0x75;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s5, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 70
    * Starting at 0x405
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x405 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x261

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x261;
      assert s1.Peek(6) == 0x75;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s5, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 55
    * Starting at 0x261
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x261 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x75;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s4, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 96
    * Starting at 0x71b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0x6a2

    requires s0.stack[13] == 0x5ce

    requires s0.stack[18] == 0x541

    requires s0.stack[22] == 0x405

    requires s0.stack[26] == 0x261

    requires s0.stack[29] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x6a2;
      assert s1.Peek(13) == 0x5ce;
      assert s1.Peek(18) == 0x541;
      assert s1.Peek(22) == 0x405;
      assert s1.Peek(26) == 0x261;
      assert s1.Peek(29) == 0x75;
      var s2 := Push2(s1, 0x05ce);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup2(s4);
      var s6 := MLoad(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0730);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s113(s9, gas - 1)
      else
        ExecuteFromCFGNode_s112(s9, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 97
    * Starting at 0x728
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x728 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[2] == 0x5ce

    requires s0.stack[8] == 0x6a2

    requires s0.stack[16] == 0x5ce

    requires s0.stack[21] == 0x541

    requires s0.stack[25] == 0x405

    requires s0.stack[29] == 0x261

    requires s0.stack[32] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(3) == 0x5ce;
      assert s1.Peek(9) == 0x6a2;
      assert s1.Peek(17) == 0x5ce;
      assert s1.Peek(22) == 0x541;
      assert s1.Peek(26) == 0x405;
      assert s1.Peek(30) == 0x261;
      assert s1.Peek(33) == 0x75;
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 113
    * Segment Id for this node is: 98
    * Starting at 0x730
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x730 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[2] == 0x5ce

    requires s0.stack[8] == 0x6a2

    requires s0.stack[16] == 0x5ce

    requires s0.stack[21] == 0x541

    requires s0.stack[25] == 0x405

    requires s0.stack[29] == 0x261

    requires s0.stack[32] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5ce;
      assert s1.Peek(8) == 0x6a2;
      assert s1.Peek(16) == 0x5ce;
      assert s1.Peek(21) == 0x541;
      assert s1.Peek(25) == 0x405;
      assert s1.Peek(29) == 0x261;
      assert s1.Peek(32) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push3(s4, 0x461bcd);
      var s6 := Push1(s5, 0xe5);
      var s7 := Shl(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x5ce;
      assert s11.Peek(10) == 0x6a2;
      assert s11.Peek(18) == 0x5ce;
      assert s11.Peek(23) == 0x541;
      assert s11.Peek(27) == 0x405;
      assert s11.Peek(31) == 0x261;
      assert s11.Peek(34) == 0x75;
      var s12 := Push2(s11, 0x0151);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x0908);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s16, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 143
    * Starting at 0x908
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x908 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[2] == 0x151

    requires s0.stack[5] == 0x5ce

    requires s0.stack[11] == 0x6a2

    requires s0.stack[19] == 0x5ce

    requires s0.stack[24] == 0x541

    requires s0.stack[28] == 0x405

    requires s0.stack[32] == 0x261

    requires s0.stack[35] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x151;
      assert s1.Peek(5) == 0x5ce;
      assert s1.Peek(11) == 0x6a2;
      assert s1.Peek(19) == 0x5ce;
      assert s1.Peek(24) == 0x541;
      assert s1.Peek(28) == 0x405;
      assert s1.Peek(32) == 0x261;
      assert s1.Peek(35) == 0x75;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push0(s4);
      var s6 := Dup3(s5);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup5(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x151;
      assert s11.Peek(9) == 0x5ce;
      assert s11.Peek(15) == 0x6a2;
      assert s11.Peek(23) == 0x5ce;
      assert s11.Peek(28) == 0x541;
      assert s11.Peek(32) == 0x405;
      assert s11.Peek(36) == 0x261;
      assert s11.Peek(39) == 0x75;
      var s12 := MStore(s11);
      var s13 := Push2(s12, 0x0926);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup8(s18);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x08cb);
      assert s21.Peek(0) == 0x8cb;
      assert s21.Peek(4) == 0x926;
      assert s21.Peek(9) == 0x151;
      assert s21.Peek(12) == 0x5ce;
      assert s21.Peek(18) == 0x6a2;
      assert s21.Peek(26) == 0x5ce;
      assert s21.Peek(31) == 0x541;
      assert s21.Peek(35) == 0x405;
      assert s21.Peek(39) == 0x261;
      assert s21.Peek(42) == 0x75;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s22, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 137
    * Starting at 0x8cb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 43

    requires s0.stack[3] == 0x926

    requires s0.stack[8] == 0x151

    requires s0.stack[11] == 0x5ce

    requires s0.stack[17] == 0x6a2

    requires s0.stack[25] == 0x5ce

    requires s0.stack[30] == 0x541

    requires s0.stack[34] == 0x405

    requires s0.stack[38] == 0x261

    requires s0.stack[41] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x926;
      assert s1.Peek(8) == 0x151;
      assert s1.Peek(11) == 0x5ce;
      assert s1.Peek(17) == 0x6a2;
      assert s1.Peek(25) == 0x5ce;
      assert s1.Peek(30) == 0x541;
      assert s1.Peek(34) == 0x405;
      assert s1.Peek(38) == 0x261;
      assert s1.Peek(41) == 0x75;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s116(s2, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 138
    * Starting at 0x8cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 44

    requires s0.stack[4] == 0x926

    requires s0.stack[9] == 0x151

    requires s0.stack[12] == 0x5ce

    requires s0.stack[18] == 0x6a2

    requires s0.stack[26] == 0x5ce

    requires s0.stack[31] == 0x541

    requires s0.stack[35] == 0x405

    requires s0.stack[39] == 0x261

    requires s0.stack[42] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x926;
      assert s1.Peek(9) == 0x151;
      assert s1.Peek(12) == 0x5ce;
      assert s1.Peek(18) == 0x6a2;
      assert s1.Peek(26) == 0x5ce;
      assert s1.Peek(31) == 0x541;
      assert s1.Peek(35) == 0x405;
      assert s1.Peek(39) == 0x261;
      assert s1.Peek(42) == 0x75;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x08e5);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s7, gas - 1)
      else
        ExecuteFromCFGNode_s117(s7, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 139
    * Starting at 0x8d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 44

    requires s0.stack[4] == 0x926

    requires s0.stack[9] == 0x151

    requires s0.stack[12] == 0x5ce

    requires s0.stack[18] == 0x6a2

    requires s0.stack[26] == 0x5ce

    requires s0.stack[31] == 0x541

    requires s0.stack[35] == 0x405

    requires s0.stack[39] == 0x261

    requires s0.stack[42] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x926;
      assert s1.Peek(10) == 0x151;
      assert s1.Peek(13) == 0x5ce;
      assert s1.Peek(19) == 0x6a2;
      assert s1.Peek(27) == 0x5ce;
      assert s1.Peek(32) == 0x541;
      assert s1.Peek(36) == 0x405;
      assert s1.Peek(40) == 0x261;
      assert s1.Peek(43) == 0x75;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x08cd);
      assert s11.Peek(0) == 0x8cd;
      assert s11.Peek(5) == 0x926;
      assert s11.Peek(10) == 0x151;
      assert s11.Peek(13) == 0x5ce;
      assert s11.Peek(19) == 0x6a2;
      assert s11.Peek(27) == 0x5ce;
      assert s11.Peek(32) == 0x541;
      assert s11.Peek(36) == 0x405;
      assert s11.Peek(40) == 0x261;
      assert s11.Peek(43) == 0x75;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s12, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 140
    * Starting at 0x8e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 44

    requires s0.stack[4] == 0x926

    requires s0.stack[9] == 0x151

    requires s0.stack[12] == 0x5ce

    requires s0.stack[18] == 0x6a2

    requires s0.stack[26] == 0x5ce

    requires s0.stack[31] == 0x541

    requires s0.stack[35] == 0x405

    requires s0.stack[39] == 0x261

    requires s0.stack[42] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x926;
      assert s1.Peek(9) == 0x151;
      assert s1.Peek(12) == 0x5ce;
      assert s1.Peek(18) == 0x6a2;
      assert s1.Peek(26) == 0x5ce;
      assert s1.Peek(31) == 0x541;
      assert s1.Peek(35) == 0x405;
      assert s1.Peek(39) == 0x261;
      assert s1.Peek(42) == 0x75;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push0(s3);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s8, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 144
    * Starting at 0x926
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x926 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[4] == 0x151

    requires s0.stack[7] == 0x5ce

    requires s0.stack[13] == 0x6a2

    requires s0.stack[21] == 0x5ce

    requires s0.stack[26] == 0x541

    requires s0.stack[30] == 0x405

    requires s0.stack[34] == 0x261

    requires s0.stack[37] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x151;
      assert s1.Peek(7) == 0x5ce;
      assert s1.Peek(13) == 0x6a2;
      assert s1.Peek(21) == 0x5ce;
      assert s1.Peek(26) == 0x541;
      assert s1.Peek(30) == 0x405;
      assert s1.Peek(34) == 0x261;
      assert s1.Peek(37) == 0x75;
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
      assert s11.Peek(4) == 0x151;
      assert s11.Peek(7) == 0x5ce;
      assert s11.Peek(13) == 0x6a2;
      assert s11.Peek(21) == 0x5ce;
      assert s11.Peek(26) == 0x541;
      assert s11.Peek(30) == 0x405;
      assert s11.Peek(34) == 0x261;
      assert s11.Peek(37) == 0x75;
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s17, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 35

    requires s0.stack[3] == 0x5ce

    requires s0.stack[9] == 0x6a2

    requires s0.stack[17] == 0x5ce

    requires s0.stack[22] == 0x541

    requires s0.stack[26] == 0x405

    requires s0.stack[30] == 0x261

    requires s0.stack[33] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ce;
      assert s1.Peek(9) == 0x6a2;
      assert s1.Peek(17) == 0x5ce;
      assert s1.Peek(22) == 0x541;
      assert s1.Peek(26) == 0x405;
      assert s1.Peek(30) == 0x261;
      assert s1.Peek(33) == 0x75;
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
    * Segment Id for this node is: 88
    * Starting at 0x68c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[10] == 0x5ce

    requires s0.stack[15] == 0x541

    requires s0.stack[19] == 0x405

    requires s0.stack[23] == 0x261

    requires s0.stack[26] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x5ce;
      assert s1.Peek(15) == 0x541;
      assert s1.Peek(19) == 0x405;
      assert s1.Peek(23) == 0x261;
      assert s1.Peek(26) == 0x75;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s88(s4, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 17
    * Starting at 0x8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b as nat
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
      var s5 := Push2(s4, 0x0096);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s124(s6, gas - 1)
      else
        ExecuteFromCFGNode_s123(s6, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 18
    * Starting at 0x93
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 124
    * Segment Id for this node is: 19
    * Starting at 0x96
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup1(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      var s12 := Sub(s11);
      var s13 := Swap1(s12);
      var s14 := Swap3(s13);
      var s15 := And(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := MLoad(s17);
      var s19 := Swap1(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      var s22 := Sub(s21);
      var s23 := Push1(s22, 0x20);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Return(s25);
      // Segment is terminal (Revert, Stop or Return)
      s26
  }

  /** Node 125
    * Segment Id for this node is: 14
    * Starting at 0x77
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77 as nat
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
      var s5 := Push2(s4, 0x0082);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s6, gas - 1)
      else
        ExecuteFromCFGNode_s126(s6, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 15
    * Starting at 0x7f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 127
    * Segment Id for this node is: 16
    * Starting at 0x82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0075);
      var s4 := Push2(s3, 0x0232);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s5, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 50
    * Starting at 0x232
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x232 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x75;
      var s2 := Push2(s1, 0x023a);
      var s3 := Push2(s2, 0x040a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s4, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 71
    * Starting at 0x40a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x23a

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x23a;
      assert s1.Peek(1) == 0x75;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x23a;
      assert s11.Peek(2) == 0x75;
      var s12 := Push2(s11, 0x0243);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s13, gas - 1)
      else
        ExecuteFromCFGNode_s130(s13, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 72
    * Starting at 0x41c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x23a

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x23a;
      assert s1.Peek(2) == 0x75;
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
      assert s11.Peek(3) == 0x23a;
      assert s11.Peek(4) == 0x75;
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
      assert s21.Peek(4) == 0x23a;
      assert s21.Peek(5) == 0x75;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x0151);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s27, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x23a

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x23a;
      assert s1.Peek(2) == 0x75;
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

  /** Node 132
    * Segment Id for this node is: 52
    * Starting at 0x243
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x23a

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x23a;
      assert s1.Peek(1) == 0x75;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s2, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 51
    * Starting at 0x23a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x75;
      var s2 := Push2(s1, 0x0243);
      var s3 := Push0(s2);
      var s4 := Push2(s3, 0x0463);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s5, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 73
    * Starting at 0x463
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x243

    requires s0.stack[2] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x243;
      assert s1.Peek(2) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup4(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x243;
      assert s11.Peek(7) == 0x75;
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
      assert s21.Peek(7) == 0x243;
      assert s21.Peek(8) == 0x75;
      var s22 := Or(s21);
      var s23 := Dup5(s22);
      var s24 := SStore(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Swap2(s26);
      var s28 := Swap1(s27);
      var s29 := Swap3(s28);
      var s30 := And(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(5) == 0x243;
      assert s31.Peek(6) == 0x75;
      var s32 := Dup4(s31);
      var s33 := Swap2(s32);
      var s34 := Push32(s33, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s35 := Swap2(s34);
      var s36 := Swap1(s35);
      var s37 := Log3(s36);
      var s38 := Pop(s37);
      var s39 := Pop(s38);
      var s40 := Jump(s39);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s40, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 52
    * Starting at 0x243
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x75;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s2, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 11
    * Starting at 0x62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0075);
      var s3 := Push2(s2, 0x0070);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0792);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s7, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 106
    * Starting at 0x792
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x792 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x70

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x70;
      assert s1.Peek(3) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := Dup6(s6);
      var s8 := Dup8(s7);
      var s9 := Sub(s8);
      var s10 := SLt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(7) == 0x70;
      assert s11.Peek(8) == 0x75;
      var s12 := Push2(s11, 0x07a5);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s13, gas - 1)
      else
        ExecuteFromCFGNode_s138(s13, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 107
    * Starting at 0x7a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x70

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x70;
      assert s1.Peek(8) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 139
    * Segment Id for this node is: 108
    * Starting at 0x7a5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x70

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x70;
      assert s1.Peek(7) == 0x75;
      var s2 := Dup5(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x07bc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s10, gas - 1)
      else
        ExecuteFromCFGNode_s140(s10, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 109
    * Starting at 0x7b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x70

    requires s0.stack[9] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(9) == 0x70;
      assert s1.Peek(10) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 141
    * Segment Id for this node is: 110
    * Starting at 0x7bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x70

    requires s0.stack[9] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x70;
      assert s1.Peek(9) == 0x75;
      var s2 := Push2(s1, 0x07c8);
      var s3 := Dup9(s2);
      var s4 := Dup4(s3);
      var s5 := Dup10(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x074a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s8, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 99
    * Starting at 0x74a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x7c8

    requires s0.stack[11] == 0x70

    requires s0.stack[12] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7c8;
      assert s1.Peek(11) == 0x70;
      assert s1.Peek(12) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x075a);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s10, gas - 1)
      else
        ExecuteFromCFGNode_s143(s10, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 100
    * Starting at 0x757
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x757 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x7c8

    requires s0.stack[13] == 0x70

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x7c8;
      assert s1.Peek(14) == 0x70;
      assert s1.Peek(15) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 144
    * Segment Id for this node is: 101
    * Starting at 0x75a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x7c8

    requires s0.stack[13] == 0x70

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7c8;
      assert s1.Peek(13) == 0x70;
      assert s1.Peek(14) == 0x75;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Push8(s4, 0xffffffffffffffff);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0771);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s146(s10, gas - 1)
      else
        ExecuteFromCFGNode_s145(s10, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 102
    * Starting at 0x76e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x7c8

    requires s0.stack[13] == 0x70

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x7c8;
      assert s1.Peek(14) == 0x70;
      assert s1.Peek(15) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 146
    * Segment Id for this node is: 103
    * Starting at 0x771
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x771 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x7c8

    requires s0.stack[13] == 0x70

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7c8;
      assert s1.Peek(13) == 0x70;
      assert s1.Peek(14) == 0x75;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x05);
      var s11 := Shl(s10);
      assert s11.Peek(7) == 0x7c8;
      assert s11.Peek(16) == 0x70;
      assert s11.Peek(17) == 0x75;
      var s12 := Dup6(s11);
      var s13 := Add(s12);
      var s14 := Add(s13);
      var s15 := Gt(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x078b);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s18, gas - 1)
      else
        ExecuteFromCFGNode_s147(s18, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 104
    * Starting at 0x788
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x788 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x7c8

    requires s0.stack[13] == 0x70

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x7c8;
      assert s1.Peek(14) == 0x70;
      assert s1.Peek(15) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 148
    * Segment Id for this node is: 105
    * Starting at 0x78b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x7c8

    requires s0.stack[13] == 0x70

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7c8;
      assert s1.Peek(13) == 0x70;
      assert s1.Peek(14) == 0x75;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s7, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 111
    * Starting at 0x7c8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x70

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x70;
      assert s1.Peek(11) == 0x75;
      var s2 := Swap1(s1);
      var s3 := Swap7(s2);
      var s4 := Pop(s3);
      var s5 := Swap5(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup8(s7);
      var s9 := Add(s8);
      var s10 := CallDataLoad(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(9) == 0x70;
      assert s11.Peek(10) == 0x75;
      var s12 := Pop(s11);
      var s13 := Dup1(s12);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x07e0);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s18, gas - 1)
      else
        ExecuteFromCFGNode_s150(s18, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 112
    * Starting at 0x7dd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x70

    requires s0.stack[9] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(9) == 0x70;
      assert s1.Peek(10) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 151
    * Segment Id for this node is: 113
    * Starting at 0x7e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x70

    requires s0.stack[9] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x70;
      assert s1.Peek(9) == 0x75;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x07ed);
      var s4 := Dup8(s3);
      var s5 := Dup3(s4);
      var s6 := Dup9(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x074a);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s9, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 99
    * Starting at 0x74a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x7ed

    requires s0.stack[10] == 0x70

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7ed;
      assert s1.Peek(10) == 0x70;
      assert s1.Peek(11) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x075a);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s154(s10, gas - 1)
      else
        ExecuteFromCFGNode_s153(s10, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 100
    * Starting at 0x757
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x757 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x7ed

    requires s0.stack[12] == 0x70

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x7ed;
      assert s1.Peek(13) == 0x70;
      assert s1.Peek(14) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 154
    * Segment Id for this node is: 101
    * Starting at 0x75a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x7ed

    requires s0.stack[12] == 0x70

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7ed;
      assert s1.Peek(12) == 0x70;
      assert s1.Peek(13) == 0x75;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Push8(s4, 0xffffffffffffffff);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0771);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s10, gas - 1)
      else
        ExecuteFromCFGNode_s155(s10, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 102
    * Starting at 0x76e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x7ed

    requires s0.stack[12] == 0x70

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x7ed;
      assert s1.Peek(13) == 0x70;
      assert s1.Peek(14) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 156
    * Segment Id for this node is: 103
    * Starting at 0x771
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x771 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x7ed

    requires s0.stack[12] == 0x70

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7ed;
      assert s1.Peek(12) == 0x70;
      assert s1.Peek(13) == 0x75;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x05);
      var s11 := Shl(s10);
      assert s11.Peek(7) == 0x7ed;
      assert s11.Peek(15) == 0x70;
      assert s11.Peek(16) == 0x75;
      var s12 := Dup6(s11);
      var s13 := Add(s12);
      var s14 := Add(s13);
      var s15 := Gt(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x078b);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s158(s18, gas - 1)
      else
        ExecuteFromCFGNode_s157(s18, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 104
    * Starting at 0x788
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x788 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x7ed

    requires s0.stack[12] == 0x70

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x7ed;
      assert s1.Peek(13) == 0x70;
      assert s1.Peek(14) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 158
    * Segment Id for this node is: 105
    * Starting at 0x78b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x7ed

    requires s0.stack[12] == 0x70

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7ed;
      assert s1.Peek(12) == 0x70;
      assert s1.Peek(13) == 0x75;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s7, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 114
    * Starting at 0x7ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x70

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x70;
      assert s1.Peek(10) == 0x75;
      var s2 := Swap6(s1);
      var s3 := Swap(s2, 9);
      var s4 := Swap5(s3);
      var s5 := Swap(s4, 8);
      var s6 := Pop(s5);
      var s7 := Swap6(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x70;
      assert s11.Peek(5) == 0x75;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s12, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 12
    * Starting at 0x70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x75;
      var s2 := Push2(s1, 0x0112);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s3, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 32
    * Starting at 0x112
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup4(s2);
      var s4 := Dup3(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x015a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s8, gas - 1)
      else
        ExecuteFromCFGNode_s162(s8, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 33
    * Starting at 0x11c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(7) == 0x75;
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
      assert s11.Peek(9) == 0x75;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0f);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 15, 0x0d8cadccee8d040dad2e6dac2e8c6d);
      var s19 := Push1(s18, 0x8b);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(9) == 0x75;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s163(s26, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x75;
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

  /** Node 164
    * Segment Id for this node is: 35
    * Starting at 0x15a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x75;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s165(s2, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 36
    * Starting at 0x15c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x75;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x01e4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s7, gas - 1)
      else
        ExecuteFromCFGNode_s166(s7, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 37
    * Starting at 0x165
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x165 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x01b6);
      assert s1.Peek(0) == 0x1b6;
      assert s1.Peek(8) == 0x75;
      var s2 := Dup6(s1);
      var s3 := Dup6(s2);
      var s4 := Dup4(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := Push2(s7, 0x0179);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s9, gas - 1)
      else
        ExecuteFromCFGNode_s167(s9, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 38
    * Starting at 0x172
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x172 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1b6

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0179);
      assert s1.Peek(0) == 0x179;
      assert s1.Peek(4) == 0x1b6;
      assert s1.Peek(12) == 0x75;
      var s2 := Push2(s1, 0x0873);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s3, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 129
    * Starting at 0x873
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x873 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x179

    requires s0.stack[4] == 0x1b6

    requires s0.stack[12] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x179;
      assert s1.Peek(4) == 0x1b6;
      assert s1.Peek(12) == 0x75;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x179;
      assert s11.Peek(6) == 0x1b6;
      assert s11.Peek(14) == 0x75;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 169
    * Segment Id for this node is: 39
    * Starting at 0x179
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x179 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1b6

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1b6;
      assert s1.Peek(11) == 0x75;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Mul(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Dup9(s7);
      var s9 := Dup9(s8);
      var s10 := Dup5(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x1b6;
      assert s11.Peek(13) == 0x75;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push2(s13, 0x0192);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s15, gas - 1)
      else
        ExecuteFromCFGNode_s170(s15, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 40
    * Starting at 0x18b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1b6

    requires s0.stack[12] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0192);
      assert s1.Peek(0) == 0x192;
      assert s1.Peek(5) == 0x1b6;
      assert s1.Peek(13) == 0x75;
      var s2 := Push2(s1, 0x0873);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s3, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 129
    * Starting at 0x873
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x873 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x192

    requires s0.stack[5] == 0x1b6

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x192;
      assert s1.Peek(5) == 0x1b6;
      assert s1.Peek(13) == 0x75;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x192;
      assert s11.Peek(7) == 0x1b6;
      assert s11.Peek(15) == 0x75;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 172
    * Segment Id for this node is: 41
    * Starting at 0x192
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x192 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1b6

    requires s0.stack[12] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1b6;
      assert s1.Peek(12) == 0x75;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Mul(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x01a7);
      assert s11.Peek(0) == 0x1a7;
      assert s11.Peek(4) == 0x1b6;
      assert s11.Peek(12) == 0x75;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0853);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s15, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 125
    * Starting at 0x853
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x853 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x1a7

    requires s0.stack[4] == 0x1b6

    requires s0.stack[12] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1a7;
      assert s1.Peek(4) == 0x1b6;
      assert s1.Peek(12) == 0x75;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0863);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s10, gas - 1)
      else
        ExecuteFromCFGNode_s174(s10, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 126
    * Starting at 0x860
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x860 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x1a7

    requires s0.stack[5] == 0x1b6

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x1a7;
      assert s1.Peek(6) == 0x1b6;
      assert s1.Peek(14) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 175
    * Segment Id for this node is: 127
    * Starting at 0x863
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x863 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x1a7

    requires s0.stack[5] == 0x1b6

    requires s0.stack[13] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1a7;
      assert s1.Peek(5) == 0x1b6;
      assert s1.Peek(13) == 0x75;
      var s2 := Push2(s1, 0x086c);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x07f9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s5, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 115
    * Starting at 0x7f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x86c

    requires s0.stack[5] == 0x1a7

    requires s0.stack[7] == 0x1b6

    requires s0.stack[15] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x86c;
      assert s1.Peek(5) == 0x1a7;
      assert s1.Peek(7) == 0x1b6;
      assert s1.Peek(15) == 0x75;
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
      assert s11.Peek(4) == 0x86c;
      assert s11.Peek(8) == 0x1a7;
      assert s11.Peek(10) == 0x1b6;
      assert s11.Peek(18) == 0x75;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x080f);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s14, gas - 1)
      else
        ExecuteFromCFGNode_s177(s14, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 116
    * Starting at 0x80c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x86c

    requires s0.stack[6] == 0x1a7

    requires s0.stack[8] == 0x1b6

    requires s0.stack[16] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x86c;
      assert s1.Peek(7) == 0x1a7;
      assert s1.Peek(9) == 0x1b6;
      assert s1.Peek(17) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 178
    * Segment Id for this node is: 117
    * Starting at 0x80f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x86c

    requires s0.stack[6] == 0x1a7

    requires s0.stack[8] == 0x1b6

    requires s0.stack[16] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x86c;
      assert s1.Peek(6) == 0x1a7;
      assert s1.Peek(8) == 0x1b6;
      assert s1.Peek(16) == 0x75;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s5, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 128
    * Starting at 0x86c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x1a7

    requires s0.stack[6] == 0x1b6

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1a7;
      assert s1.Peek(6) == 0x1b6;
      assert s1.Peek(14) == 0x75;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s7, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 42
    * Starting at 0x1a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x1b6

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b6;
      assert s1.Peek(10) == 0x75;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Swap1(s7);
      var s9 := Push2(s8, 0x02f0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s10, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 63
    * Starting at 0x2f0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x1b6

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b6;
      assert s1.Peek(10) == 0x75;
      var s2 := Dup1(s1);
      var s3 := SelfBalance(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0340);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s184(s7, gas - 1)
      else
        ExecuteFromCFGNode_s182(s7, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 64
    * Starting at 0x2f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x1b6

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x1b6;
      assert s1.Peek(11) == 0x75;
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
      assert s11.Peek(5) == 0x1b6;
      assert s11.Peek(13) == 0x75;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a20696e73756666696369656e742062616c616e6365000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x1b6;
      assert s21.Peek(13) == 0x75;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x0151);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s26, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1b6

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1b6;
      assert s1.Peek(11) == 0x75;
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

  /** Node 184
    * Segment Id for this node is: 65
    * Starting at 0x340
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x1b6

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b6;
      assert s1.Peek(10) == 0x75;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Dup3(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(6) == 0x1b6;
      assert s11.Peek(14) == 0x75;
      var s12 := MLoad(s11);
      var s13 := Push0(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := MLoad(s14);
      var s16 := Dup1(s15);
      var s17 := Dup4(s16);
      var s18 := Sub(s17);
      var s19 := Dup2(s18);
      var s20 := Dup6(s19);
      var s21 := Dup8(s20);
      assert s21.Peek(12) == 0x1b6;
      assert s21.Peek(20) == 0x75;
      var s22 := Gas(s21);
      var s23 := Call(s22);
      var s24 := Swap3(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := ReturnDataSize(s27);
      var s29 := Dup1(s28);
      var s30 := Push0(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(8) == 0x1b6;
      assert s31.Peek(16) == 0x75;
      var s32 := Eq(s31);
      var s33 := Push2(s32, 0x0389);
      var s34 := JumpI(s33);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s33.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s34, gas - 1)
      else
        ExecuteFromCFGNode_s185(s34, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 66
    * Starting at 0x369
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x369 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1b6

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(7) == 0x1b6;
      assert s1.Peek(15) == 0x75;
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
      assert s11.Peek(8) == 0x1b6;
      assert s11.Peek(16) == 0x75;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push0(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(10) == 0x1b6;
      assert s21.Peek(18) == 0x75;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x038e);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s25, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 68
    * Starting at 0x38e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1b6

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1b6;
      assert s1.Peek(14) == 0x75;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Dup1(s5);
      var s7 := Push2(s6, 0x0405);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s8, gas - 1)
      else
        ExecuteFromCFGNode_s187(s8, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 69
    * Starting at 0x398
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x398 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1b6

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x1b6;
      assert s1.Peek(12) == 0x75;
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
      assert s11.Peek(6) == 0x1b6;
      assert s11.Peek(14) == 0x75;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x3a);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a20756e61626c6520746f2073656e642076616c75652c2072);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x1b6;
      assert s21.Peek(14) == 0x75;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6563697069656e74206d61792068617665207265766572746564000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0151);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s31, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1b6

    requires s0.stack[12] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1b6;
      assert s1.Peek(12) == 0x75;
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

  /** Node 189
    * Segment Id for this node is: 70
    * Starting at 0x405
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x405 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1b6

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1b6;
      assert s1.Peek(11) == 0x75;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s5, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 43
    * Starting at 0x1b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x75;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Dup3(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := Push2(s7, 0x01c8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s9, gas - 1)
      else
        ExecuteFromCFGNode_s191(s9, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 44
    * Starting at 0x1c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x01c8);
      assert s1.Peek(0) == 0x1c8;
      assert s1.Peek(11) == 0x75;
      var s2 := Push2(s1, 0x0873);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s3, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 129
    * Starting at 0x873
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x873 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x1c8

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1c8;
      assert s1.Peek(11) == 0x75;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x1c8;
      assert s11.Peek(13) == 0x75;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 193
    * Segment Id for this node is: 45
    * Starting at 0x1c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x75;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Mul(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Dup4(s7);
      var s9 := Push2(s8, 0x01da);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x1da;
      assert s11.Peek(10) == 0x75;
      var s12 := Push2(s11, 0x0887);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s13, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 130
    * Starting at 0x887
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x887 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x1da

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1da;
      assert s1.Peek(10) == 0x75;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x08a6);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s196(s10, gas - 1)
      else
        ExecuteFromCFGNode_s195(s10, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 131
    * Starting at 0x893
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x893 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1da

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x1da;
      assert s1.Peek(12) == 0x75;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 196
    * Segment Id for this node is: 132
    * Starting at 0x8a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1da

    requires s0.stack[11] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1da;
      assert s1.Peek(11) == 0x75;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s6, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 46
    * Starting at 0x1da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x75;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Add(s4);
      var s6 := Push2(s5, 0x015c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s7, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 67
    * Starting at 0x389
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x389 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1b6

    requires s0.stack[14] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1b6;
      assert s1.Peek(14) == 0x75;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s186(s4, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 47
    * Starting at 0x1e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x75;
      var s2 := Pop(s1);
      var s3 := CallValue(s2);
      var s4 := Dup3(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x022a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s8, gas - 1)
      else
        ExecuteFromCFGNode_s200(s8, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 48
    * Starting at 0x1ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(7) == 0x75;
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
      assert s11.Peek(9) == 0x75;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x12);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 18, 0x696e73756666696369656e742066756e6473);
      var s19 := Push1(s18, 0x70);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(9) == 0x75;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0151);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s28, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 49
    * Starting at 0x22a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x75;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s8, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 8
    * Starting at 0x57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x005e);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s4, gas - 1)
      else
        ExecuteFromCFGNode_s203(s4, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 9
    * Starting at 0x5d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d as nat
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

  /** Node 204
    * Segment Id for this node is: 10
    * Starting at 0x5e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e as nat
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
