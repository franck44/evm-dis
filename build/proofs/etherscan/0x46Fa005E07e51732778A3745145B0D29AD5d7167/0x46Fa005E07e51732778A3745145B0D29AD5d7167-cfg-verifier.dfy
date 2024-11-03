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
      var s6 := Push2(s5, 0x00b4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s225(s7, gas - 1)
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
      var s6 := Push4(s5, 0x56f36dbf);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x0071);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s9, gas - 1)
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
      var s2 := Push4(s1, 0x56f36dbf);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0249);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s5, gas - 1)
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
      var s2 := Push4(s1, 0x6684b1d6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02c6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s5, gas - 1)
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
      var s2 := Push4(s1, 0x8757653f);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02ce);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s5, gas - 1)
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
      var s2 := Push4(s1, 0xb449ea5d);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02f4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s5, gas - 1)
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
      var s2 := Push4(s1, 0xeeb72866);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x032e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s5, gas - 1)
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
      var s2 := Push4(s1, 0xf9bcdde4);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0336);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 10
    * Starting at 0x6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
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
      var s1 := Push2(s0, 0x00b4);
      assert s1.Peek(0) == 0xb4;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s2, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 17
    * Starting at 0xb4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4 as nat
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

  /** Node 12
    * Segment Id for this node is: 64
    * Starting at 0x336
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x336 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0139);
      var s3 := Push2(s2, 0x0688);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s4, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 93
    * Starting at 0x688
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x688 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      var s2 := Push2(s1, 0x0635);
      var s3 := Push2(s2, 0x0a55);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s4, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 126
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x635

    requires s0.stack[1] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x635;
      assert s1.Peek(1) == 0x139;
      var s2 := Push2(s1, 0x0a5e);
      var s3 := Caller(s2);
      var s4 := Push2(s3, 0x0690);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s5, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 94
    * Starting at 0x690
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x690 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0xa5e

    requires s0.stack[2] == 0x635

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa5e;
      assert s1.Peek(2) == 0x635;
      assert s1.Peek(3) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x069b);
      var s5 := Push2(s4, 0x0aff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s6, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x69b

    requires s0.stack[4] == 0xa5e

    requires s0.stack[5] == 0x635

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x69b;
      assert s1.Peek(4) == 0xa5e;
      assert s1.Peek(5) == 0x635;
      assert s1.Peek(6) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x69b;
      assert s11.Peek(8) == 0xa5e;
      assert s11.Peek(9) == 0x635;
      assert s11.Peek(10) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x69b;
      assert s21.Peek(8) == 0xa5e;
      assert s21.Peek(9) == 0x635;
      assert s21.Peek(10) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x69b;
      assert s31.Peek(12) == 0xa5e;
      assert s31.Peek(13) == 0x635;
      assert s31.Peek(14) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s17(s33, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0xa5e

    requires s0.stack[15] == 0x635

    requires s0.stack[16] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0xa5e;
      assert s1.Peek(15) == 0x635;
      assert s1.Peek(16) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s6, gas - 1)
      else
        ExecuteFromCFGNode_s18(s6, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0xa5e

    requires s0.stack[15] == 0x635

    requires s0.stack[16] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x69b;
      assert s1.Peek(15) == 0xa5e;
      assert s1.Peek(16) == 0x635;
      assert s1.Peek(17) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x69b;
      assert s11.Peek(15) == 0xa5e;
      assert s11.Peek(16) == 0x635;
      assert s11.Peek(17) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s18, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0xa5e

    requires s0.stack[15] == 0x635

    requires s0.stack[16] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0xa5e;
      assert s1.Peek(15) == 0x635;
      assert s1.Peek(16) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x69b;
      assert s11.Peek(17) == 0xa5e;
      assert s11.Peek(18) == 0x635;
      assert s11.Peek(19) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x69b;
      assert s21.Peek(14) == 0xa5e;
      assert s21.Peek(15) == 0x635;
      assert s21.Peek(16) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x69b;
      assert s31.Peek(10) == 0xa5e;
      assert s31.Peek(11) == 0x635;
      assert s31.Peek(12) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s20(s41, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x69b

    requires s0.stack[8] == 0xa5e

    requires s0.stack[9] == 0x635

    requires s0.stack[10] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x69b;
      assert s1.Peek(7) == 0xa5e;
      assert s1.Peek(8) == 0x635;
      assert s1.Peek(9) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s4, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 95
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0xa5e

    requires s0.stack[5] == 0x635

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa5e;
      assert s1.Peek(5) == 0x635;
      assert s1.Peek(6) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap4(s6);
      var s8 := Swap1(s7);
      var s9 := Swap4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0xa5e;
      assert s11.Peek(6) == 0x635;
      assert s11.Peek(7) == 0x139;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap4(s15);
      var s17 := Swap1(s16);
      var s18 := Swap4(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0xa5e;
      assert s21.Peek(2) == 0x635;
      assert s21.Peek(3) == 0x139;
      var s22 := Push1(s21, 0x40);
      var s23 := Swap1(s22);
      var s24 := Keccak256(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s29, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 127
    * Starting at 0xa5e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x635

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x635;
      assert s1.Peek(2) == 0x139;
      var s2 := Push2(s1, 0x0aa1);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s3, gas - 1)
      else
        ExecuteFromCFGNode_s23(s3, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 128
    * Starting at 0xa63
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x635

    requires s0.stack[1] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x635;
      assert s1.Peek(2) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(5) == 0x635;
      assert s11.Peek(6) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x0f);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 15, 0x4f4e4c595f474f5645524e414e4345);
      var s20 := Push1(s19, 0x88);
      var s21 := Shl(s20);
      assert s21.Peek(3) == 0x635;
      assert s21.Peek(4) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(2) == 0x635;
      assert s31.Peek(3) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 24
    * Segment Id for this node is: 129
    * Starting at 0xaa1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x635

    requires s0.stack[1] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x635;
      assert s1.Peek(1) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0aab);
      var s4 := Push2(s3, 0x0aff);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s5, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0xaab

    requires s0.stack[2] == 0x635

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xaab;
      assert s1.Peek(2) == 0x635;
      assert s1.Peek(3) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0xaab;
      assert s11.Peek(6) == 0x635;
      assert s11.Peek(7) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0xaab;
      assert s21.Peek(6) == 0x635;
      assert s21.Peek(7) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0xaab;
      assert s31.Peek(10) == 0x635;
      assert s31.Peek(11) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s26(s33, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0xaab

    requires s0.stack[12] == 0x635

    requires s0.stack[13] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xaab;
      assert s1.Peek(12) == 0x635;
      assert s1.Peek(13) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s6, gas - 1)
      else
        ExecuteFromCFGNode_s27(s6, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0xaab

    requires s0.stack[12] == 0x635

    requires s0.stack[13] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0xaab;
      assert s1.Peek(13) == 0x635;
      assert s1.Peek(14) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0xaab;
      assert s11.Peek(13) == 0x635;
      assert s11.Peek(14) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s18, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0xaab

    requires s0.stack[12] == 0x635

    requires s0.stack[13] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xaab;
      assert s1.Peek(12) == 0x635;
      assert s1.Peek(13) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0xaab;
      assert s11.Peek(15) == 0x635;
      assert s11.Peek(16) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0xaab;
      assert s21.Peek(12) == 0x635;
      assert s21.Peek(13) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0xaab;
      assert s31.Peek(8) == 0x635;
      assert s31.Peek(9) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s29(s41, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xaab

    requires s0.stack[6] == 0x635

    requires s0.stack[7] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaab;
      assert s1.Peek(5) == 0x635;
      assert s1.Peek(6) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s4, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 130
    * Starting at 0xaab
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x635

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x635;
      assert s1.Peek(3) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(5) == 0x635;
      assert s11.Peek(6) == 0x139;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x05a6);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s17, gas - 1)
      else
        ExecuteFromCFGNode_s31(s17, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 131
    * Starting at 0xac2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x635

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(2) == 0x635;
      assert s1.Peek(3) == 0x139;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Not(s10);
      assert s11.Peek(4) == 0x635;
      assert s11.Peek(5) == 0x139;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := SStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Push32(s16, 0x7a8dc7dd7fffb43c4807438fa62729225156941e641fd877938f4edade3429f5);
      var s18 := Swap1(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Swap1(s19);
      var s21 := Log1(s20);
      assert s21.Peek(1) == 0x635;
      assert s21.Peek(2) == 0x139;
      var s22 := Pop(s21);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s23, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 88
    * Starting at 0x635
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x635 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s2, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 27
    * Starting at 0x139
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
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

  /** Node 34
    * Segment Id for this node is: 82
    * Starting at 0x5a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x635

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x635;
      assert s1.Peek(2) == 0x139;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s3, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 63
    * Starting at 0x32e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0251);
      var s3 := Push2(s2, 0x0651);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s4, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 92
    * Starting at 0x651
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x651 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x251

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x251;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x1b);
      assert s11.Peek(2) == 0x251;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push32(s13, 0x537461726b576172655f50726f78795574696c735f323032325f320000000000);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Swap1(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s20, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 49
    * Starting at 0x251
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x251 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Dup4(s8);
      var s10 := MLoad(s9);
      var s11 := Dup2(s10);
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup4(s14);
      var s16 := MLoad(s15);
      var s17 := Swap2(s16);
      var s18 := Swap3(s17);
      var s19 := Dup4(s18);
      var s20 := Swap3(s19);
      var s21 := Swap1(s20);
      var s22 := Dup4(s21);
      var s23 := Add(s22);
      var s24 := Swap2(s23);
      var s25 := Dup6(s24);
      var s26 := Add(s25);
      var s27 := Swap1(s26);
      var s28 := Dup1(s27);
      var s29 := Dup4(s28);
      var s30 := Dup4(s29);
      var s31 := Push1(s30, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s38(s31, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 50
    * Starting at 0x273
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x028b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s40(s7, gas - 1)
      else
        ExecuteFromCFGNode_s39(s7, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 51
    * Starting at 0x27c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0273);
      assert s11.Peek(0) == 0x273;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s12, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 52
    * Starting at 0x28b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      var s12 := Push1(s11, 0x1f);
      var s13 := And(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x02b8);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s17, gas - 1)
      else
        ExecuteFromCFGNode_s41(s17, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 53
    * Starting at 0x29f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Dup3(s1);
      var s3 := Sub(s2);
      var s4 := Dup1(s3);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Sub(s8);
      var s10 := Push2(s9, 0x0100);
      var s11 := Exp(s10);
      var s12 := Sub(s11);
      var s13 := Not(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Swap2(s18);
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s42(s20, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 54
    * Starting at 0x2b8
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Swap2(s9);
      var s11 := Sub(s10);
      var s12 := Swap1(s11);
      var s13 := Return(s12);
      // Segment is terminal (Revert, Stop or Return)
      s13
  }

  /** Node 43
    * Segment Id for this node is: 59
    * Starting at 0x2f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x031a);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x030a);
      assert s11.Peek(0) == 0x30a;
      assert s11.Peek(4) == 0x31a;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s12, gas - 1)
      else
        ExecuteFromCFGNode_s44(s12, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 60
    * Starting at 0x306
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x306 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x31a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 45
    * Segment Id for this node is: 61
    * Starting at 0x30a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31a;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Push2(s9, 0x0640);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s11, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 90
    * Starting at 0x640
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x640 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x31a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x064b);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0690);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s6, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 94
    * Starting at 0x690
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x690 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x64b

    requires s0.stack[4] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64b;
      assert s1.Peek(4) == 0x31a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x069b);
      var s5 := Push2(s4, 0x0aff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s6, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x69b

    requires s0.stack[4] == 0x64b

    requires s0.stack[7] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x69b;
      assert s1.Peek(4) == 0x64b;
      assert s1.Peek(7) == 0x31a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x69b;
      assert s11.Peek(8) == 0x64b;
      assert s11.Peek(11) == 0x31a;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x69b;
      assert s21.Peek(8) == 0x64b;
      assert s21.Peek(11) == 0x31a;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x69b;
      assert s31.Peek(12) == 0x64b;
      assert s31.Peek(15) == 0x31a;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s49(s33, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x64b

    requires s0.stack[17] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x64b;
      assert s1.Peek(17) == 0x31a;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s6, gas - 1)
      else
        ExecuteFromCFGNode_s50(s6, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x64b

    requires s0.stack[17] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x69b;
      assert s1.Peek(15) == 0x64b;
      assert s1.Peek(18) == 0x31a;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x69b;
      assert s11.Peek(15) == 0x64b;
      assert s11.Peek(18) == 0x31a;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s18, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x64b

    requires s0.stack[17] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x64b;
      assert s1.Peek(17) == 0x31a;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x69b;
      assert s11.Peek(17) == 0x64b;
      assert s11.Peek(20) == 0x31a;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x69b;
      assert s21.Peek(14) == 0x64b;
      assert s21.Peek(17) == 0x31a;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x69b;
      assert s31.Peek(10) == 0x64b;
      assert s31.Peek(13) == 0x31a;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s52(s41, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x69b

    requires s0.stack[8] == 0x64b

    requires s0.stack[11] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x69b;
      assert s1.Peek(7) == 0x64b;
      assert s1.Peek(10) == 0x31a;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s4, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 95
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x64b

    requires s0.stack[7] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x64b;
      assert s1.Peek(7) == 0x31a;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap4(s6);
      var s8 := Swap1(s7);
      var s9 := Swap4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x64b;
      assert s11.Peek(8) == 0x31a;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap4(s15);
      var s17 := Swap1(s16);
      var s18 := Swap4(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x64b;
      assert s21.Peek(4) == 0x31a;
      var s22 := Push1(s21, 0x40);
      var s23 := Swap1(s22);
      var s24 := Keccak256(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s29, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 91
    * Starting at 0x64b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x31a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x31a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s6, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 62
    * Starting at 0x31a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := IsZero(s5);
      var s7 := IsZero(s6);
      var s8 := Dup3(s7);
      var s9 := MStore(s8);
      var s10 := MLoad(s9);
      var s11 := Swap1(s10);
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := Sub(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Return(s17);
      // Segment is terminal (Revert, Stop or Return)
      s18
  }

  /** Node 56
    * Segment Id for this node is: 56
    * Starting at 0x2ce
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0139);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x02e4);
      assert s11.Peek(0) == 0x2e4;
      assert s11.Peek(4) == 0x139;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s12, gas - 1)
      else
        ExecuteFromCFGNode_s57(s12, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 57
    * Starting at 0x2e0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 58
    * Segment Id for this node is: 58
    * Starting at 0x2e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Push2(s9, 0x0637);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s11, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 89
    * Starting at 0x637
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x637 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x139;
      var s2 := Push2(s1, 0x05a6);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x08b5);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s5, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 113
    * Starting at 0x8b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5a6

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5a6;
      assert s1.Peek(3) == 0x139;
      var s2 := Push2(s1, 0x08be);
      var s3 := Caller(s2);
      var s4 := Push2(s3, 0x0690);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s5, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 94
    * Starting at 0x690
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x690 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x8be

    requires s0.stack[3] == 0x5a6

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8be;
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x069b);
      var s5 := Push2(s4, 0x0aff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s6, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x69b

    requires s0.stack[4] == 0x8be

    requires s0.stack[6] == 0x5a6

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x69b;
      assert s1.Peek(4) == 0x8be;
      assert s1.Peek(6) == 0x5a6;
      assert s1.Peek(8) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x69b;
      assert s11.Peek(8) == 0x8be;
      assert s11.Peek(10) == 0x5a6;
      assert s11.Peek(12) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x69b;
      assert s21.Peek(8) == 0x8be;
      assert s21.Peek(10) == 0x5a6;
      assert s21.Peek(12) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x69b;
      assert s31.Peek(12) == 0x8be;
      assert s31.Peek(14) == 0x5a6;
      assert s31.Peek(16) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s63(s33, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x8be

    requires s0.stack[16] == 0x5a6

    requires s0.stack[18] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x8be;
      assert s1.Peek(16) == 0x5a6;
      assert s1.Peek(18) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s6, gas - 1)
      else
        ExecuteFromCFGNode_s64(s6, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x8be

    requires s0.stack[16] == 0x5a6

    requires s0.stack[18] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x69b;
      assert s1.Peek(15) == 0x8be;
      assert s1.Peek(17) == 0x5a6;
      assert s1.Peek(19) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x69b;
      assert s11.Peek(15) == 0x8be;
      assert s11.Peek(17) == 0x5a6;
      assert s11.Peek(19) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s18, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x8be

    requires s0.stack[16] == 0x5a6

    requires s0.stack[18] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x8be;
      assert s1.Peek(16) == 0x5a6;
      assert s1.Peek(18) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x69b;
      assert s11.Peek(17) == 0x8be;
      assert s11.Peek(19) == 0x5a6;
      assert s11.Peek(21) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x69b;
      assert s21.Peek(14) == 0x8be;
      assert s21.Peek(16) == 0x5a6;
      assert s21.Peek(18) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x69b;
      assert s31.Peek(10) == 0x8be;
      assert s31.Peek(12) == 0x5a6;
      assert s31.Peek(14) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s66(s41, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x69b

    requires s0.stack[8] == 0x8be

    requires s0.stack[10] == 0x5a6

    requires s0.stack[12] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x69b;
      assert s1.Peek(7) == 0x8be;
      assert s1.Peek(9) == 0x5a6;
      assert s1.Peek(11) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s4, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 95
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x8be

    requires s0.stack[6] == 0x5a6

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x8be;
      assert s1.Peek(6) == 0x5a6;
      assert s1.Peek(8) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap4(s6);
      var s8 := Swap1(s7);
      var s9 := Swap4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x8be;
      assert s11.Peek(7) == 0x5a6;
      assert s11.Peek(9) == 0x139;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap4(s15);
      var s17 := Swap1(s16);
      var s18 := Swap4(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x8be;
      assert s21.Peek(3) == 0x5a6;
      assert s21.Peek(5) == 0x139;
      var s22 := Push1(s21, 0x40);
      var s23 := Swap1(s22);
      var s24 := Keccak256(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s29, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 114
    * Starting at 0x8be
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a6;
      assert s1.Peek(4) == 0x139;
      var s2 := Push2(s1, 0x0901);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s3, gas - 1)
      else
        ExecuteFromCFGNode_s69(s3, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 115
    * Starting at 0x8c3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5a6

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x5a6;
      assert s1.Peek(4) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(6) == 0x5a6;
      assert s11.Peek(8) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x0f);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 15, 0x4f4e4c595f474f5645524e414e4345);
      var s20 := Push1(s19, 0x88);
      var s21 := Shl(s20);
      assert s21.Peek(4) == 0x5a6;
      assert s21.Peek(6) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(3) == 0x5a6;
      assert s31.Peek(5) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 70
    * Segment Id for this node is: 116
    * Starting at 0x901
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x901 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5a6

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5a6;
      assert s1.Peek(3) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x090b);
      var s4 := Push2(s3, 0x0aff);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s5, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x90b

    requires s0.stack[3] == 0x5a6

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x90b;
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x90b;
      assert s11.Peek(7) == 0x5a6;
      assert s11.Peek(9) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x90b;
      assert s21.Peek(7) == 0x5a6;
      assert s21.Peek(9) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x90b;
      assert s31.Peek(11) == 0x5a6;
      assert s31.Peek(13) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s72(s33, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[10] == 0x90b

    requires s0.stack[13] == 0x5a6

    requires s0.stack[15] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x90b;
      assert s1.Peek(13) == 0x5a6;
      assert s1.Peek(15) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s6, gas - 1)
      else
        ExecuteFromCFGNode_s73(s6, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[10] == 0x90b

    requires s0.stack[13] == 0x5a6

    requires s0.stack[15] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x90b;
      assert s1.Peek(14) == 0x5a6;
      assert s1.Peek(16) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x90b;
      assert s11.Peek(14) == 0x5a6;
      assert s11.Peek(16) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s18, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[10] == 0x90b

    requires s0.stack[13] == 0x5a6

    requires s0.stack[15] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x90b;
      assert s1.Peek(13) == 0x5a6;
      assert s1.Peek(15) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x90b;
      assert s11.Peek(16) == 0x5a6;
      assert s11.Peek(18) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x90b;
      assert s21.Peek(13) == 0x5a6;
      assert s21.Peek(15) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x90b;
      assert s31.Peek(9) == 0x5a6;
      assert s31.Peek(11) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s75(s41, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x90b

    requires s0.stack[7] == 0x5a6

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x90b;
      assert s1.Peek(6) == 0x5a6;
      assert s1.Peek(8) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s4, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 117
    * Starting at 0x90b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x5a6

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Push2(s10, 0x0956);
      assert s11.Peek(0) == 0x956;
      assert s11.Peek(4) == 0x5a6;
      assert s11.Peek(6) == 0x139;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s12, gas - 1)
      else
        ExecuteFromCFGNode_s77(s12, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 118
    * Starting at 0x91c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(7) == 0x5a6;
      assert s11.Peek(9) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x0b);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 11, 0x4241445f41444452455353);
      var s20 := Push1(s19, 0xa8);
      var s21 := Shl(s20);
      assert s21.Peek(5) == 0x5a6;
      assert s21.Peek(7) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(4) == 0x5a6;
      assert s31.Peek(6) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 78
    * Segment Id for this node is: 119
    * Starting at 0x956
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x956 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a6;
      assert s1.Peek(4) == 0x139;
      var s2 := Push2(s1, 0x095f);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0690);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s5, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 94
    * Starting at 0x690
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x690 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x95f

    requires s0.stack[4] == 0x5a6

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x95f;
      assert s1.Peek(4) == 0x5a6;
      assert s1.Peek(6) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x069b);
      var s5 := Push2(s4, 0x0aff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s6, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x69b

    requires s0.stack[4] == 0x95f

    requires s0.stack[7] == 0x5a6

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x69b;
      assert s1.Peek(4) == 0x95f;
      assert s1.Peek(7) == 0x5a6;
      assert s1.Peek(9) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x69b;
      assert s11.Peek(8) == 0x95f;
      assert s11.Peek(11) == 0x5a6;
      assert s11.Peek(13) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x69b;
      assert s21.Peek(8) == 0x95f;
      assert s21.Peek(11) == 0x5a6;
      assert s21.Peek(13) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x69b;
      assert s31.Peek(12) == 0x95f;
      assert s31.Peek(15) == 0x5a6;
      assert s31.Peek(17) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s81(s33, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x95f

    requires s0.stack[17] == 0x5a6

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x95f;
      assert s1.Peek(17) == 0x5a6;
      assert s1.Peek(19) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s6, gas - 1)
      else
        ExecuteFromCFGNode_s82(s6, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x95f

    requires s0.stack[17] == 0x5a6

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x69b;
      assert s1.Peek(15) == 0x95f;
      assert s1.Peek(18) == 0x5a6;
      assert s1.Peek(20) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x69b;
      assert s11.Peek(15) == 0x95f;
      assert s11.Peek(18) == 0x5a6;
      assert s11.Peek(20) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s18, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x95f

    requires s0.stack[17] == 0x5a6

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x95f;
      assert s1.Peek(17) == 0x5a6;
      assert s1.Peek(19) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x69b;
      assert s11.Peek(17) == 0x95f;
      assert s11.Peek(20) == 0x5a6;
      assert s11.Peek(22) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x69b;
      assert s21.Peek(14) == 0x95f;
      assert s21.Peek(17) == 0x5a6;
      assert s21.Peek(19) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x69b;
      assert s31.Peek(10) == 0x95f;
      assert s31.Peek(13) == 0x5a6;
      assert s31.Peek(15) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s84(s41, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x69b

    requires s0.stack[8] == 0x95f

    requires s0.stack[11] == 0x5a6

    requires s0.stack[13] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x69b;
      assert s1.Peek(7) == 0x95f;
      assert s1.Peek(10) == 0x5a6;
      assert s1.Peek(12) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s4, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 95
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x95f

    requires s0.stack[7] == 0x5a6

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x95f;
      assert s1.Peek(7) == 0x5a6;
      assert s1.Peek(9) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap4(s6);
      var s8 := Swap1(s7);
      var s9 := Swap4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x95f;
      assert s11.Peek(8) == 0x5a6;
      assert s11.Peek(10) == 0x139;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap4(s15);
      var s17 := Swap1(s16);
      var s18 := Swap4(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x95f;
      assert s21.Peek(4) == 0x5a6;
      assert s21.Peek(6) == 0x139;
      var s22 := Push1(s21, 0x40);
      var s23 := Swap1(s22);
      var s24 := Keccak256(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s29, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 120
    * Starting at 0x95f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x5a6

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x09a4);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s4, gas - 1)
      else
        ExecuteFromCFGNode_s87(s4, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 121
    * Starting at 0x965
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x965 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(7) == 0x5a6;
      assert s11.Peek(9) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x10);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 16, 0x20a62922a0a22cafa3a7ab22a92727a9);
      var s20 := Push1(s19, 0x81);
      var s21 := Shl(s20);
      assert s21.Peek(5) == 0x5a6;
      assert s21.Peek(7) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(4) == 0x5a6;
      assert s31.Peek(6) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 88
    * Segment Id for this node is: 122
    * Starting at 0x9a4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a6;
      assert s1.Peek(4) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(3) == 0x5a6;
      assert s11.Peek(5) == 0x139;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x09fe);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s14, gas - 1)
      else
        ExecuteFromCFGNode_s89(s14, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 123
    * Starting at 0x9b8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(7) == 0x5a6;
      assert s11.Peek(9) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x17);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 23, 0x4f544845525f43414e4449444154455f50454e44494e47);
      var s20 := Push1(s19, 0x48);
      var s21 := Shl(s20);
      assert s21.Peek(5) == 0x5a6;
      assert s21.Peek(7) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(4) == 0x5a6;
      assert s31.Peek(6) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 90
    * Segment Id for this node is: 124
    * Starting at 0x9fe
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a6;
      assert s1.Peek(4) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := SLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x5a6;
      assert s11.Peek(7) == 0x139;
      var s12 := Dup5(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := Not(s18);
      var s20 := Swap1(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(6) == 0x5a6;
      assert s21.Peek(8) == 0x139;
      var s22 := And(s21);
      var s23 := Dup2(s22);
      var s24 := Or(s23);
      var s25 := Swap1(s24);
      var s26 := Swap2(s25);
      var s27 := SStore(s26);
      var s28 := Push1(s27, 0x40);
      var s29 := Dup1(s28);
      var s30 := MLoad(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(5) == 0x5a6;
      assert s31.Peek(7) == 0x139;
      var s32 := Dup3(s31);
      var s33 := MStore(s32);
      var s34 := MLoad(s33);
      var s35 := Push32(s34, 0x6166272c8d3f5f579082f2827532732f97195007983bb5b83ac12c56700b01a6);
      var s36 := Swap2(s35);
      var s37 := Dup2(s36);
      var s38 := Swap1(s37);
      var s39 := Sub(s38);
      var s40 := Push1(s39, 0x20);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s91(s41, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 125
    * Starting at 0xa50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x5a6

    requires s0.stack[7] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(5) == 0x5a6;
      assert s1.Peek(7) == 0x139;
      var s2 := Log1(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s5, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 82
    * Starting at 0x5a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x139;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s3, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 55
    * Starting at 0x2c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0139);
      var s3 := Push2(s2, 0x062d);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s4, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 87
    * Starting at 0x62d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x139;
      var s2 := Push2(s1, 0x0635);
      var s3 := Push2(s2, 0x0831);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s4, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 108
    * Starting at 0x831
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x831 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x635

    requires s0.stack[1] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x635;
      assert s1.Peek(1) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x083b);
      var s4 := Push2(s3, 0x0aff);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s5, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x83b

    requires s0.stack[2] == 0x635

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x83b;
      assert s1.Peek(2) == 0x635;
      assert s1.Peek(3) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x83b;
      assert s11.Peek(6) == 0x635;
      assert s11.Peek(7) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x83b;
      assert s21.Peek(6) == 0x635;
      assert s21.Peek(7) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x83b;
      assert s31.Peek(10) == 0x635;
      assert s31.Peek(11) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s97(s33, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0x83b

    requires s0.stack[12] == 0x635

    requires s0.stack[13] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x83b;
      assert s1.Peek(12) == 0x635;
      assert s1.Peek(13) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s99(s6, gas - 1)
      else
        ExecuteFromCFGNode_s98(s6, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0x83b

    requires s0.stack[12] == 0x635

    requires s0.stack[13] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x83b;
      assert s1.Peek(13) == 0x635;
      assert s1.Peek(14) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x83b;
      assert s11.Peek(13) == 0x635;
      assert s11.Peek(14) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s18, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0x83b

    requires s0.stack[12] == 0x635

    requires s0.stack[13] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x83b;
      assert s1.Peek(12) == 0x635;
      assert s1.Peek(13) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x83b;
      assert s11.Peek(15) == 0x635;
      assert s11.Peek(16) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x83b;
      assert s21.Peek(12) == 0x635;
      assert s21.Peek(13) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x83b;
      assert s31.Peek(8) == 0x635;
      assert s31.Peek(9) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s100(s41, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x83b

    requires s0.stack[6] == 0x635

    requires s0.stack[7] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x83b;
      assert s1.Peek(5) == 0x635;
      assert s1.Peek(6) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s4, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 109
    * Starting at 0x83b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x635

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x635;
      assert s1.Peek(3) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(5) == 0x635;
      assert s11.Peek(6) == 0x139;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Caller(s14);
      var s16 := Eq(s15);
      var s17 := Push2(s16, 0x0899);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s18, gas - 1)
      else
        ExecuteFromCFGNode_s102(s18, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 110
    * Starting at 0x853
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x853 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x635

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x635;
      assert s1.Peek(3) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(6) == 0x635;
      assert s11.Peek(7) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x17);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 23, 0x27a7262cafa1a0a72224a220aa22afa3a7ab22a92727a9);
      var s20 := Push1(s19, 0x49);
      var s21 := Shl(s20);
      assert s21.Peek(4) == 0x635;
      assert s21.Peek(5) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(3) == 0x635;
      assert s31.Peek(4) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 103
    * Segment Id for this node is: 111
    * Starting at 0x899
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x899 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x635

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x635;
      assert s1.Peek(2) == 0x139;
      var s2 := Push2(s1, 0x08a2);
      var s3 := Caller(s2);
      var s4 := Push2(s3, 0x0b7c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s5, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 137
    * Starting at 0xb7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x8a2

    requires s0.stack[3] == 0x635

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8a2;
      assert s1.Peek(3) == 0x635;
      assert s1.Peek(4) == 0x139;
      var s2 := Push2(s1, 0x0b85);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0690);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s5, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 94
    * Starting at 0x690
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x690 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0xb85

    requires s0.stack[3] == 0x8a2

    requires s0.stack[5] == 0x635

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb85;
      assert s1.Peek(3) == 0x8a2;
      assert s1.Peek(5) == 0x635;
      assert s1.Peek(6) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x069b);
      var s5 := Push2(s4, 0x0aff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s6, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x69b

    requires s0.stack[4] == 0xb85

    requires s0.stack[6] == 0x8a2

    requires s0.stack[8] == 0x635

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x69b;
      assert s1.Peek(4) == 0xb85;
      assert s1.Peek(6) == 0x8a2;
      assert s1.Peek(8) == 0x635;
      assert s1.Peek(9) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x69b;
      assert s11.Peek(8) == 0xb85;
      assert s11.Peek(10) == 0x8a2;
      assert s11.Peek(12) == 0x635;
      assert s11.Peek(13) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x69b;
      assert s21.Peek(8) == 0xb85;
      assert s21.Peek(10) == 0x8a2;
      assert s21.Peek(12) == 0x635;
      assert s21.Peek(13) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x69b;
      assert s31.Peek(12) == 0xb85;
      assert s31.Peek(14) == 0x8a2;
      assert s31.Peek(16) == 0x635;
      assert s31.Peek(17) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s107(s33, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0xb85

    requires s0.stack[16] == 0x8a2

    requires s0.stack[18] == 0x635

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0xb85;
      assert s1.Peek(16) == 0x8a2;
      assert s1.Peek(18) == 0x635;
      assert s1.Peek(19) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s109(s6, gas - 1)
      else
        ExecuteFromCFGNode_s108(s6, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0xb85

    requires s0.stack[16] == 0x8a2

    requires s0.stack[18] == 0x635

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x69b;
      assert s1.Peek(15) == 0xb85;
      assert s1.Peek(17) == 0x8a2;
      assert s1.Peek(19) == 0x635;
      assert s1.Peek(20) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x69b;
      assert s11.Peek(15) == 0xb85;
      assert s11.Peek(17) == 0x8a2;
      assert s11.Peek(19) == 0x635;
      assert s11.Peek(20) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s18, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0xb85

    requires s0.stack[16] == 0x8a2

    requires s0.stack[18] == 0x635

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0xb85;
      assert s1.Peek(16) == 0x8a2;
      assert s1.Peek(18) == 0x635;
      assert s1.Peek(19) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x69b;
      assert s11.Peek(17) == 0xb85;
      assert s11.Peek(19) == 0x8a2;
      assert s11.Peek(21) == 0x635;
      assert s11.Peek(22) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x69b;
      assert s21.Peek(14) == 0xb85;
      assert s21.Peek(16) == 0x8a2;
      assert s21.Peek(18) == 0x635;
      assert s21.Peek(19) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x69b;
      assert s31.Peek(10) == 0xb85;
      assert s31.Peek(12) == 0x8a2;
      assert s31.Peek(14) == 0x635;
      assert s31.Peek(15) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s110(s41, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x69b

    requires s0.stack[8] == 0xb85

    requires s0.stack[10] == 0x8a2

    requires s0.stack[12] == 0x635

    requires s0.stack[13] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x69b;
      assert s1.Peek(7) == 0xb85;
      assert s1.Peek(9) == 0x8a2;
      assert s1.Peek(11) == 0x635;
      assert s1.Peek(12) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s4, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 95
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xb85

    requires s0.stack[6] == 0x8a2

    requires s0.stack[8] == 0x635

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb85;
      assert s1.Peek(6) == 0x8a2;
      assert s1.Peek(8) == 0x635;
      assert s1.Peek(9) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap4(s6);
      var s8 := Swap1(s7);
      var s9 := Swap4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0xb85;
      assert s11.Peek(7) == 0x8a2;
      assert s11.Peek(9) == 0x635;
      assert s11.Peek(10) == 0x139;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap4(s15);
      var s17 := Swap1(s16);
      var s18 := Swap4(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0xb85;
      assert s21.Peek(3) == 0x8a2;
      assert s21.Peek(5) == 0x635;
      assert s21.Peek(6) == 0x139;
      var s22 := Push1(s21, 0x40);
      var s23 := Swap1(s22);
      var s24 := Keccak256(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s29, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 138
    * Starting at 0xb85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x8a2

    requires s0.stack[4] == 0x635

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8a2;
      assert s1.Peek(4) == 0x635;
      assert s1.Peek(5) == 0x139;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0bca);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s4, gas - 1)
      else
        ExecuteFromCFGNode_s113(s4, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 139
    * Starting at 0xb8b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x8a2

    requires s0.stack[3] == 0x635

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x8a2;
      assert s1.Peek(4) == 0x635;
      assert s1.Peek(5) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(6) == 0x8a2;
      assert s11.Peek(8) == 0x635;
      assert s11.Peek(9) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x10);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 16, 0x20a62922a0a22cafa3a7ab22a92727a9);
      var s20 := Push1(s19, 0x81);
      var s21 := Shl(s20);
      assert s21.Peek(4) == 0x8a2;
      assert s21.Peek(6) == 0x635;
      assert s21.Peek(7) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(3) == 0x8a2;
      assert s31.Peek(5) == 0x635;
      assert s31.Peek(6) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 114
    * Segment Id for this node is: 140
    * Starting at 0xbca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x8a2

    requires s0.stack[3] == 0x635

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8a2;
      assert s1.Peek(3) == 0x635;
      assert s1.Peek(4) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0bd4);
      var s4 := Push2(s3, 0x0aff);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s5, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xbd4

    requires s0.stack[3] == 0x8a2

    requires s0.stack[5] == 0x635

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xbd4;
      assert s1.Peek(3) == 0x8a2;
      assert s1.Peek(5) == 0x635;
      assert s1.Peek(6) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0xbd4;
      assert s11.Peek(7) == 0x8a2;
      assert s11.Peek(9) == 0x635;
      assert s11.Peek(10) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0xbd4;
      assert s21.Peek(7) == 0x8a2;
      assert s21.Peek(9) == 0x635;
      assert s21.Peek(10) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0xbd4;
      assert s31.Peek(11) == 0x8a2;
      assert s31.Peek(13) == 0x635;
      assert s31.Peek(14) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s116(s33, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[10] == 0xbd4

    requires s0.stack[13] == 0x8a2

    requires s0.stack[15] == 0x635

    requires s0.stack[16] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xbd4;
      assert s1.Peek(13) == 0x8a2;
      assert s1.Peek(15) == 0x635;
      assert s1.Peek(16) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s6, gas - 1)
      else
        ExecuteFromCFGNode_s117(s6, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[10] == 0xbd4

    requires s0.stack[13] == 0x8a2

    requires s0.stack[15] == 0x635

    requires s0.stack[16] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0xbd4;
      assert s1.Peek(14) == 0x8a2;
      assert s1.Peek(16) == 0x635;
      assert s1.Peek(17) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0xbd4;
      assert s11.Peek(14) == 0x8a2;
      assert s11.Peek(16) == 0x635;
      assert s11.Peek(17) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s18, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[10] == 0xbd4

    requires s0.stack[13] == 0x8a2

    requires s0.stack[15] == 0x635

    requires s0.stack[16] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xbd4;
      assert s1.Peek(13) == 0x8a2;
      assert s1.Peek(15) == 0x635;
      assert s1.Peek(16) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0xbd4;
      assert s11.Peek(16) == 0x8a2;
      assert s11.Peek(18) == 0x635;
      assert s11.Peek(19) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0xbd4;
      assert s21.Peek(13) == 0x8a2;
      assert s21.Peek(15) == 0x635;
      assert s21.Peek(16) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0xbd4;
      assert s31.Peek(9) == 0x8a2;
      assert s31.Peek(11) == 0x635;
      assert s31.Peek(12) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s119(s41, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xbd4

    requires s0.stack[7] == 0x8a2

    requires s0.stack[9] == 0x635

    requires s0.stack[10] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xbd4;
      assert s1.Peek(6) == 0x8a2;
      assert s1.Peek(8) == 0x635;
      assert s1.Peek(9) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s4, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 141
    * Starting at 0xbd4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x8a2

    requires s0.stack[5] == 0x635

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8a2;
      assert s1.Peek(5) == 0x635;
      assert s1.Peek(6) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x8a2;
      assert s11.Peek(9) == 0x635;
      assert s11.Peek(10) == 0x139;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup4(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap2(s17);
      var s19 := Dup3(s18);
      var s20 := Swap1(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(7) == 0x8a2;
      assert s21.Peek(9) == 0x635;
      assert s21.Peek(10) == 0x139;
      var s22 := Dup1(s21);
      var s23 := SLoad(s22);
      var s24 := Push1(s23, 0xff);
      var s25 := Not(s24);
      var s26 := And(s25);
      var s27 := Push1(s26, 0x01);
      var s28 := Or(s27);
      var s29 := Swap1(s28);
      var s30 := SStore(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(7) == 0x8a2;
      assert s31.Peek(9) == 0x635;
      assert s31.Peek(10) == 0x139;
      var s32 := MLoad(s31);
      var s33 := Swap3(s32);
      var s34 := Dup4(s33);
      var s35 := MStore(s34);
      var s36 := Swap1(s35);
      var s37 := MLoad(s36);
      var s38 := Swap3(s37);
      var s39 := Swap4(s38);
      var s40 := Pop(s39);
      var s41 := Push32(s40, 0xcfb473e6c03f9a29ddaf990e736fa3de5188a0bd85d684f5b6e164ebfbfff5d2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s121(s41, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 142
    * Starting at 0xc25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x8a2

    requires s0.stack[8] == 0x635

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap3(s0);
      assert s1.Peek(6) == 0x8a2;
      assert s1.Peek(8) == 0x635;
      assert s1.Peek(9) == 0x139;
      var s2 := Swap2(s1);
      var s3 := Dup3(s2);
      var s4 := Swap1(s3);
      var s5 := Sub(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Log1(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s11, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 112
    * Starting at 0x8a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x635

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x635;
      assert s1.Peek(2) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Add(s2);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Not(s10);
      assert s11.Peek(3) == 0x635;
      assert s11.Peek(4) == 0x139;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := SStore(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s15, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 48
    * Starting at 0x249
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x249 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0251);
      var s3 := Push2(s2, 0x0611);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s4, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 86
    * Starting at 0x611
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x611 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x251

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x251;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MStore(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x27);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x251;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0c31);
      var s16 := Push1(s15, 0x27);
      var s17 := Swap2(s16);
      var s18 := CodeCopy(s17);
      var s19 := Dup2(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s20, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 49
    * Starting at 0x251
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x251 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x251

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x251;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Dup4(s8);
      var s10 := MLoad(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x251;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup4(s14);
      var s16 := MLoad(s15);
      var s17 := Swap2(s16);
      var s18 := Swap3(s17);
      var s19 := Dup4(s18);
      var s20 := Swap3(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(6) == 0x251;
      var s22 := Dup4(s21);
      var s23 := Add(s22);
      var s24 := Swap2(s23);
      var s25 := Dup6(s24);
      var s26 := Add(s25);
      var s27 := Swap1(s26);
      var s28 := Dup1(s27);
      var s29 := Dup4(s28);
      var s30 := Dup4(s29);
      var s31 := Push1(s30, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s126(s31, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 50
    * Starting at 0x273
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x251

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x251;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x028b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s128(s7, gas - 1)
      else
        ExecuteFromCFGNode_s127(s7, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 51
    * Starting at 0x27c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x251

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(11) == 0x251;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0273);
      assert s11.Peek(0) == 0x273;
      assert s11.Peek(11) == 0x251;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s12, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 52
    * Starting at 0x28b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x251

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x251;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(5) == 0x251;
      var s12 := Push1(s11, 0x1f);
      var s13 := And(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x02b8);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s17, gas - 1)
      else
        ExecuteFromCFGNode_s129(s17, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 53
    * Starting at 0x29f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x251

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(6) == 0x251;
      var s2 := Dup3(s1);
      var s3 := Sub(s2);
      var s4 := Dup1(s3);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Sub(s8);
      var s10 := Push2(s9, 0x0100);
      var s11 := Exp(s10);
      assert s11.Peek(9) == 0x251;
      var s12 := Sub(s11);
      var s13 := Not(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Swap2(s18);
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s130(s20, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 54
    * Starting at 0x2b8
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x251

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x251;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Swap2(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0x251;
      var s12 := Swap1(s11);
      var s13 := Return(s12);
      // Segment is terminal (Revert, Stop or Return)
      s13
  }

  /** Node 131
    * Segment Id for this node is: 11
    * Starting at 0x71
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0x02a93fae);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00b9);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s6, gas - 1)
      else
        ExecuteFromCFGNode_s132(s6, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x0ebdac03);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x013b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s187(s5, gas - 1)
      else
        ExecuteFromCFGNode_s133(s5, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x12f16e6d);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0193);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s153(s5, gas - 1)
      else
        ExecuteFromCFGNode_s134(s5, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 14
    * Starting at 0x93
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x20cea94d);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01b9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s150(s5, gas - 1)
      else
        ExecuteFromCFGNode_s135(s5, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 15
    * Starting at 0x9e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x3cc660ad);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01d3);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s147(s5, gas - 1)
      else
        ExecuteFromCFGNode_s136(s5, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 16
    * Starting at 0xa9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x439fab91);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01db);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s5, gas - 1)
      else
        ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 39
    * Starting at 0x1db
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0139);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x01f1);
      assert s11.Peek(0) == 0x1f1;
      assert s11.Peek(4) == 0x139;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s12, gas - 1)
      else
        ExecuteFromCFGNode_s138(s12, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 40
    * Starting at 0x1ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 139
    * Segment Id for this node is: 41
    * Starting at 0x1f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup2(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(6) == 0x139;
      var s12 := Shl(s11);
      var s13 := Dup2(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x020b);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s17, gas - 1)
      else
        ExecuteFromCFGNode_s140(s17, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 42
    * Starting at 0x207
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x207 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 141
    * Segment Id for this node is: 43
    * Starting at 0x20b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x139;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x021d);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s11, gas - 1)
      else
        ExecuteFromCFGNode_s142(s11, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 44
    * Starting at 0x219
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x219 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 143
    * Segment Id for this node is: 45
    * Starting at 0x21d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x139;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap2(s6);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Dup4(s9);
      var s11 := Mul(s10);
      assert s11.Peek(7) == 0x139;
      var s12 := Dup5(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0x20);
      var s17 := Shl(s16);
      var s18 := Dup4(s17);
      var s19 := Gt(s18);
      var s20 := Or(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(6) == 0x139;
      var s22 := Push2(s21, 0x023e);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s23, gas - 1)
      else
        ExecuteFromCFGNode_s144(s23, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 46
    * Starting at 0x23a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 145
    * Segment Id for this node is: 47
    * Starting at 0x23e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x139;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x05d2);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s9, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 85
    * Starting at 0x5d2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push3(s4, 0x461bcd);
      var s6 := Push1(s5, 0xe5);
      var s7 := Shl(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x04);
      assert s11.Peek(6) == 0x139;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x0f);
      var s16 := Push1(s15, 0x24);
      var s17 := Dup3(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := PushN(s19, 15, 0x1393d517d253541311535153951151);
      var s21 := Push1(s20, 0x8a);
      assert s21.Peek(6) == 0x139;
      var s22 := Shl(s21);
      var s23 := Push1(s22, 0x44);
      var s24 := Dup3(s23);
      var s25 := Add(s24);
      var s26 := MStore(s25);
      var s27 := Swap1(s26);
      var s28 := MLoad(s27);
      var s29 := Swap1(s28);
      var s30 := Dup2(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x139;
      var s32 := Sub(s31);
      var s33 := Push1(s32, 0x64);
      var s34 := Add(s33);
      var s35 := Swap1(s34);
      var s36 := Revert(s35);
      // Segment is terminal (Revert, Stop or Return)
      s36
  }

  /** Node 147
    * Segment Id for this node is: 38
    * Starting at 0x1d3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01c1);
      var s3 := Push2(s2, 0x05cd);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s4, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 84
    * Starting at 0x5cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1c1;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s4, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 37
    * Starting at 0x1c1
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      var s12 := Sub(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Swap1(s14);
      var s16 := Return(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 150
    * Segment Id for this node is: 36
    * Starting at 0x1b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01c1);
      var s3 := Push2(s2, 0x05a9);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s4, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 83
    * Starting at 0x5a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1c1;
      var s2 := Push32(s1, 0xc21dbb3089fcb2c4f4c6a67854ab4db2b0f233ea4b21b21f912d52d18fc5db1f);
      var s3 := Dup2(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s4, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 37
    * Starting at 0x1c1
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1c1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1c1;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(3) == 0x1c1;
      var s12 := Sub(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Swap1(s14);
      var s16 := Return(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 153
    * Segment Id for this node is: 33
    * Starting at 0x193
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x193 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0139);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x01a9);
      assert s11.Peek(0) == 0x1a9;
      assert s11.Peek(4) == 0x139;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s155(s12, gas - 1)
      else
        ExecuteFromCFGNode_s154(s12, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 34
    * Starting at 0x1a5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 155
    * Segment Id for this node is: 35
    * Starting at 0x1a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Push2(s9, 0x059d);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s11, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 81
    * Starting at 0x59d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x139;
      var s2 := Push2(s1, 0x05a6);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x06e4);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s5, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 97
    * Starting at 0x6e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5a6

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5a6;
      assert s1.Peek(3) == 0x139;
      var s2 := Push2(s1, 0x06ed);
      var s3 := Caller(s2);
      var s4 := Push2(s3, 0x0690);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s5, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 94
    * Starting at 0x690
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x690 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x6ed

    requires s0.stack[3] == 0x5a6

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6ed;
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x069b);
      var s5 := Push2(s4, 0x0aff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s6, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x69b

    requires s0.stack[4] == 0x6ed

    requires s0.stack[6] == 0x5a6

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x69b;
      assert s1.Peek(4) == 0x6ed;
      assert s1.Peek(6) == 0x5a6;
      assert s1.Peek(8) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x69b;
      assert s11.Peek(8) == 0x6ed;
      assert s11.Peek(10) == 0x5a6;
      assert s11.Peek(12) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x69b;
      assert s21.Peek(8) == 0x6ed;
      assert s21.Peek(10) == 0x5a6;
      assert s21.Peek(12) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x69b;
      assert s31.Peek(12) == 0x6ed;
      assert s31.Peek(14) == 0x5a6;
      assert s31.Peek(16) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s160(s33, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x6ed

    requires s0.stack[16] == 0x5a6

    requires s0.stack[18] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x6ed;
      assert s1.Peek(16) == 0x5a6;
      assert s1.Peek(18) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s162(s6, gas - 1)
      else
        ExecuteFromCFGNode_s161(s6, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x6ed

    requires s0.stack[16] == 0x5a6

    requires s0.stack[18] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x69b;
      assert s1.Peek(15) == 0x6ed;
      assert s1.Peek(17) == 0x5a6;
      assert s1.Peek(19) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x69b;
      assert s11.Peek(15) == 0x6ed;
      assert s11.Peek(17) == 0x5a6;
      assert s11.Peek(19) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s18, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x6ed

    requires s0.stack[16] == 0x5a6

    requires s0.stack[18] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x6ed;
      assert s1.Peek(16) == 0x5a6;
      assert s1.Peek(18) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x69b;
      assert s11.Peek(17) == 0x6ed;
      assert s11.Peek(19) == 0x5a6;
      assert s11.Peek(21) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x69b;
      assert s21.Peek(14) == 0x6ed;
      assert s21.Peek(16) == 0x5a6;
      assert s21.Peek(18) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x69b;
      assert s31.Peek(10) == 0x6ed;
      assert s31.Peek(12) == 0x5a6;
      assert s31.Peek(14) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s163(s41, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x69b

    requires s0.stack[8] == 0x6ed

    requires s0.stack[10] == 0x5a6

    requires s0.stack[12] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x69b;
      assert s1.Peek(7) == 0x6ed;
      assert s1.Peek(9) == 0x5a6;
      assert s1.Peek(11) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s4, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 95
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x6ed

    requires s0.stack[6] == 0x5a6

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6ed;
      assert s1.Peek(6) == 0x5a6;
      assert s1.Peek(8) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap4(s6);
      var s8 := Swap1(s7);
      var s9 := Swap4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x6ed;
      assert s11.Peek(7) == 0x5a6;
      assert s11.Peek(9) == 0x139;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap4(s15);
      var s17 := Swap1(s16);
      var s18 := Swap4(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x6ed;
      assert s21.Peek(3) == 0x5a6;
      assert s21.Peek(5) == 0x139;
      var s22 := Push1(s21, 0x40);
      var s23 := Swap1(s22);
      var s24 := Keccak256(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s29, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 98
    * Starting at 0x6ed
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a6;
      assert s1.Peek(4) == 0x139;
      var s2 := Push2(s1, 0x0730);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s167(s3, gas - 1)
      else
        ExecuteFromCFGNode_s166(s3, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 99
    * Starting at 0x6f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5a6

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x5a6;
      assert s1.Peek(4) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(6) == 0x5a6;
      assert s11.Peek(8) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x0f);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 15, 0x4f4e4c595f474f5645524e414e4345);
      var s20 := Push1(s19, 0x88);
      var s21 := Shl(s20);
      assert s21.Peek(4) == 0x5a6;
      assert s21.Peek(6) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(3) == 0x5a6;
      assert s31.Peek(5) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 167
    * Segment Id for this node is: 100
    * Starting at 0x730
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x730 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5a6

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5a6;
      assert s1.Peek(3) == 0x139;
      var s2 := Caller(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup3(s7);
      var s9 := And(s8);
      var s10 := Eq(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(2) == 0x5a6;
      assert s11.Peek(4) == 0x139;
      var s12 := Push2(s11, 0x0785);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s13, gas - 1)
      else
        ExecuteFromCFGNode_s168(s13, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 101
    * Starting at 0x742
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x742 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5a6

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x5a6;
      assert s1.Peek(4) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(6) == 0x5a6;
      assert s11.Peek(8) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x14);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push20(s18, 0x474f5645524e4f525f53454c465f52454d4f5645);
      var s20 := Push1(s19, 0x60);
      var s21 := Shl(s20);
      assert s21.Peek(4) == 0x5a6;
      assert s21.Peek(6) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(3) == 0x5a6;
      assert s31.Peek(5) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 169
    * Segment Id for this node is: 102
    * Starting at 0x785
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x785 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5a6

    requires s0.stack[3] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5a6;
      assert s1.Peek(3) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x078f);
      var s4 := Push2(s3, 0x0aff);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s5, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x78f

    requires s0.stack[3] == 0x5a6

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x78f;
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x78f;
      assert s11.Peek(7) == 0x5a6;
      assert s11.Peek(9) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x78f;
      assert s21.Peek(7) == 0x5a6;
      assert s21.Peek(9) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x78f;
      assert s31.Peek(11) == 0x5a6;
      assert s31.Peek(13) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s171(s33, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[10] == 0x78f

    requires s0.stack[13] == 0x5a6

    requires s0.stack[15] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x78f;
      assert s1.Peek(13) == 0x5a6;
      assert s1.Peek(15) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s173(s6, gas - 1)
      else
        ExecuteFromCFGNode_s172(s6, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[10] == 0x78f

    requires s0.stack[13] == 0x5a6

    requires s0.stack[15] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x78f;
      assert s1.Peek(14) == 0x5a6;
      assert s1.Peek(16) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x78f;
      assert s11.Peek(14) == 0x5a6;
      assert s11.Peek(16) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s18, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[10] == 0x78f

    requires s0.stack[13] == 0x5a6

    requires s0.stack[15] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x78f;
      assert s1.Peek(13) == 0x5a6;
      assert s1.Peek(15) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x78f;
      assert s11.Peek(16) == 0x5a6;
      assert s11.Peek(18) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x78f;
      assert s21.Peek(13) == 0x5a6;
      assert s21.Peek(15) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x78f;
      assert s31.Peek(9) == 0x5a6;
      assert s31.Peek(11) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s174(s41, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x78f

    requires s0.stack[7] == 0x5a6

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x78f;
      assert s1.Peek(6) == 0x5a6;
      assert s1.Peek(8) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s4, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 103
    * Starting at 0x78f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x5a6

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x079a);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0690);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s7, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 94
    * Starting at 0x690
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x690 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x79a

    requires s0.stack[4] == 0x5a6

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x79a;
      assert s1.Peek(4) == 0x5a6;
      assert s1.Peek(6) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x069b);
      var s5 := Push2(s4, 0x0aff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s6, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x69b

    requires s0.stack[4] == 0x79a

    requires s0.stack[7] == 0x5a6

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x69b;
      assert s1.Peek(4) == 0x79a;
      assert s1.Peek(7) == 0x5a6;
      assert s1.Peek(9) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x69b;
      assert s11.Peek(8) == 0x79a;
      assert s11.Peek(11) == 0x5a6;
      assert s11.Peek(13) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x69b;
      assert s21.Peek(8) == 0x79a;
      assert s21.Peek(11) == 0x5a6;
      assert s21.Peek(13) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x69b;
      assert s31.Peek(12) == 0x79a;
      assert s31.Peek(15) == 0x5a6;
      assert s31.Peek(17) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s178(s33, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x79a

    requires s0.stack[17] == 0x5a6

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x79a;
      assert s1.Peek(17) == 0x5a6;
      assert s1.Peek(19) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s180(s6, gas - 1)
      else
        ExecuteFromCFGNode_s179(s6, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x79a

    requires s0.stack[17] == 0x5a6

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x69b;
      assert s1.Peek(15) == 0x79a;
      assert s1.Peek(18) == 0x5a6;
      assert s1.Peek(20) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x69b;
      assert s11.Peek(15) == 0x79a;
      assert s11.Peek(18) == 0x5a6;
      assert s11.Peek(20) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s18, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x79a

    requires s0.stack[17] == 0x5a6

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x79a;
      assert s1.Peek(17) == 0x5a6;
      assert s1.Peek(19) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x69b;
      assert s11.Peek(17) == 0x79a;
      assert s11.Peek(20) == 0x5a6;
      assert s11.Peek(22) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x69b;
      assert s21.Peek(14) == 0x79a;
      assert s21.Peek(17) == 0x5a6;
      assert s21.Peek(19) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x69b;
      assert s31.Peek(10) == 0x79a;
      assert s31.Peek(13) == 0x5a6;
      assert s31.Peek(15) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s181(s41, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x69b

    requires s0.stack[8] == 0x79a

    requires s0.stack[11] == 0x5a6

    requires s0.stack[13] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x69b;
      assert s1.Peek(7) == 0x79a;
      assert s1.Peek(10) == 0x5a6;
      assert s1.Peek(12) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s4, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 95
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x79a

    requires s0.stack[7] == 0x5a6

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x79a;
      assert s1.Peek(7) == 0x5a6;
      assert s1.Peek(9) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap4(s6);
      var s8 := Swap1(s7);
      var s9 := Swap4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x79a;
      assert s11.Peek(8) == 0x5a6;
      assert s11.Peek(10) == 0x139;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap4(s15);
      var s17 := Swap1(s16);
      var s18 := Swap4(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x79a;
      assert s21.Peek(4) == 0x5a6;
      assert s21.Peek(6) == 0x139;
      var s22 := Push1(s21, 0x40);
      var s23 := Swap1(s22);
      var s24 := Keccak256(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s29, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 104
    * Starting at 0x79a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x5a6

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Push2(s1, 0x07da);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s185(s3, gas - 1)
      else
        ExecuteFromCFGNode_s184(s3, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 105
    * Starting at 0x79f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(7) == 0x5a6;
      assert s11.Peek(9) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x0c);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 12, 0x2727aa2fa3a7ab22a92727a9);
      var s20 := Push1(s19, 0xa1);
      var s21 := Shl(s20);
      assert s21.Peek(5) == 0x5a6;
      assert s21.Peek(7) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(4) == 0x5a6;
      assert s31.Peek(6) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 185
    * Segment Id for this node is: 106
    * Starting at 0x7da
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a6;
      assert s1.Peek(4) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x5a6;
      assert s11.Peek(8) == 0x139;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup4(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap2(s17);
      var s19 := Dup3(s18);
      var s20 := Swap1(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(6) == 0x5a6;
      assert s21.Peek(8) == 0x139;
      var s22 := Dup1(s21);
      var s23 := SLoad(s22);
      var s24 := Push1(s23, 0xff);
      var s25 := Not(s24);
      var s26 := And(s25);
      var s27 := Swap1(s26);
      var s28 := SStore(s27);
      var s29 := Dup2(s28);
      var s30 := MLoad(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(6) == 0x5a6;
      assert s31.Peek(8) == 0x139;
      var s32 := Dup4(s31);
      var s33 := MStore(s32);
      var s34 := Swap1(s33);
      var s35 := MLoad(s34);
      var s36 := Push32(s35, 0xd75f94825e770b8b512be8e74759e252ad00e102e38f50cce2f7c6f868a29599);
      var s37 := Swap3(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := Sub(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s186(s41, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 107
    * Starting at 0x82a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x5a6

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(6) == 0x5a6;
      assert s1.Peek(8) == 0x139;
      var s2 := Add(s1);
      var s3 := Swap1(s2);
      var s4 := Log1(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s7, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 28
    * Starting at 0x13b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0143);
      var s3 := Push2(s2, 0x058b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s4, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 80
    * Starting at 0x58b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x143

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x143;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(3) == 0x143;
      var s12 := Swap2(s11);
      var s13 := MStore(s12);
      var s14 := Swap1(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s15, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 29
    * Starting at 0x143
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Dup4(s8);
      var s10 := MLoad(s9);
      var s11 := Dup2(s10);
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup4(s14);
      var s16 := MLoad(s15);
      var s17 := Swap2(s16);
      var s18 := Swap3(s17);
      var s19 := Dup4(s18);
      var s20 := Swap3(s19);
      var s21 := Swap1(s20);
      var s22 := Dup4(s21);
      var s23 := Add(s22);
      var s24 := Swap2(s23);
      var s25 := Dup6(s24);
      var s26 := Dup2(s25);
      var s27 := Add(s26);
      var s28 := Swap2(s27);
      var s29 := Mul(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      var s32 := Dup4(s31);
      var s33 := Push1(s32, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s190(s33, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 30
    * Starting at 0x167
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x167 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x017f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s192(s7, gas - 1)
      else
        ExecuteFromCFGNode_s191(s7, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 31
    * Starting at 0x170
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x170 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0167);
      assert s11.Peek(0) == 0x167;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s12, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 32
    * Starting at 0x17f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -10
    * Net Capacity Effect: +10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Add(s7);
      var s9 := Swap3(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      var s12 := Pop(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Dup1(s14);
      var s16 := Swap2(s15);
      var s17 := Sub(s16);
      var s18 := Swap1(s17);
      var s19 := Return(s18);
      // Segment is terminal (Revert, Stop or Return)
      s19
  }

  /** Node 193
    * Segment Id for this node is: 18
    * Starting at 0xb9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0139);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x00cf);
      assert s11.Peek(0) == 0xcf;
      assert s11.Peek(4) == 0x139;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s12, gas - 1)
      else
        ExecuteFromCFGNode_s194(s12, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 19
    * Starting at 0xcb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 195
    * Segment Id for this node is: 20
    * Starting at 0xcf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := CallDataLoad(s7);
      var s9 := And(s8);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(3) == 0x139;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := CallDataLoad(s20);
      assert s21.Peek(5) == 0x139;
      var s22 := Push1(s21, 0x01);
      var s23 := Push1(s22, 0x20);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := Gt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x00f9);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s29, gas - 1)
      else
        ExecuteFromCFGNode_s196(s29, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 21
    * Starting at 0xf5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 197
    * Segment Id for this node is: 22
    * Starting at 0xf9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x139;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x010b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s11, gas - 1)
      else
        ExecuteFromCFGNode_s198(s11, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 23
    * Starting at 0x107
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 199
    * Segment Id for this node is: 24
    * Starting at 0x10b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x139;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap2(s6);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Dup4(s9);
      var s11 := Mul(s10);
      assert s11.Peek(8) == 0x139;
      var s12 := Dup5(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0x20);
      var s17 := Shl(s16);
      var s18 := Dup4(s17);
      var s19 := Gt(s18);
      var s20 := Or(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0x139;
      var s22 := Push2(s21, 0x012c);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s23, gas - 1)
      else
        ExecuteFromCFGNode_s200(s23, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 25
    * Starting at 0x128
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 201
    * Segment Id for this node is: 26
    * Starting at 0x12c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x139;
      var s2 := Swap2(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := CallDataLoad(s6);
      var s8 := IsZero(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x033e);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s11, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 65
    * Starting at 0x33e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x139;
      var s2 := Push2(s1, 0x0347);
      var s3 := Caller(s2);
      var s4 := Push2(s3, 0x0690);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s5, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 94
    * Starting at 0x690
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x690 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x347

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x347;
      assert s1.Peek(6) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x069b);
      var s5 := Push2(s4, 0x0aff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s6, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 132
    * Starting at 0xaff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x69b

    requires s0.stack[4] == 0x347

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x69b;
      assert s1.Peek(4) == 0x347;
      assert s1.Peek(9) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x69b;
      assert s11.Peek(8) == 0x347;
      assert s11.Peek(13) == 0x139;
      var s12 := Push1(s11, 0x27);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0c31);
      var s18 := Push1(s17, 0x27);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x69b;
      assert s21.Peek(8) == 0x347;
      assert s21.Peek(13) == 0x139;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup3(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(8) == 0x69b;
      assert s31.Peek(12) == 0x347;
      assert s31.Peek(17) == 0x139;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s205(s33, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 133
    * Starting at 0xb2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x347

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x347;
      assert s1.Peek(19) == 0x139;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b4a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s207(s6, gas - 1)
      else
        ExecuteFromCFGNode_s206(s6, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 134
    * Starting at 0xb34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x347

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(11) == 0x69b;
      assert s1.Peek(15) == 0x347;
      assert s1.Peek(20) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x69b;
      assert s11.Peek(15) == 0x347;
      assert s11.Peek(20) == 0x139;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0b2b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s18, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 135
    * Starting at 0xb4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x69b

    requires s0.stack[14] == 0x347

    requires s0.stack[19] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x69b;
      assert s1.Peek(14) == 0x347;
      assert s1.Peek(19) == 0x139;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(13) == 0x69b;
      assert s11.Peek(17) == 0x347;
      assert s11.Peek(22) == 0x139;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(10) == 0x69b;
      assert s21.Peek(14) == 0x347;
      assert s21.Peek(19) == 0x139;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Swap3(s23);
      var s25 := Add(s24);
      var s26 := Swap5(s25);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Pop(s28);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(6) == 0x69b;
      assert s31.Peek(10) == 0x347;
      assert s31.Peek(15) == 0x139;
      var s32 := Swap4(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Sub(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Keccak256(s38);
      var s40 := Swap4(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s208(s41, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 136
    * Starting at 0xb78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x69b

    requires s0.stack[8] == 0x347

    requires s0.stack[13] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x69b;
      assert s1.Peek(7) == 0x347;
      assert s1.Peek(12) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s4, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 95
    * Starting at 0x69b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x347

    requires s0.stack[9] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x347;
      assert s1.Peek(9) == 0x139;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap4(s6);
      var s8 := Swap1(s7);
      var s9 := Swap4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x347;
      assert s11.Peek(10) == 0x139;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap4(s15);
      var s17 := Swap1(s16);
      var s18 := Swap4(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x347;
      assert s21.Peek(6) == 0x139;
      var s22 := Push1(s21, 0x40);
      var s23 := Swap1(s22);
      var s24 := Keccak256(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s29, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 66
    * Starting at 0x347
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x347 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x139;
      var s2 := Push2(s1, 0x038a);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s3, gas - 1)
      else
        ExecuteFromCFGNode_s211(s3, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 67
    * Starting at 0x34c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x0f);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 15, 0x4f4e4c595f474f5645524e414e4345);
      var s20 := Push1(s19, 0x88);
      var s21 := Shl(s20);
      assert s21.Peek(7) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(6) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 212
    * Segment Id for this node is: 68
    * Starting at 0x38a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0394);
      var s4 := Push2(s3, 0x06bf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s5, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 96
    * Starting at 0x6bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x394

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x394;
      assert s1.Peek(6) == 0x139;
      var s2 := Push32(s1, 0xc21dbb3089fcb2c4f4c6a67854ab4db2b0f233ea4b21b21f912d52d18fc5db1f);
      var s3 := SLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s5, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 69
    * Starting at 0x394
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x394 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x139;
      var s2 := TimeStamp(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Dup5(s6);
      var s8 := Dup5(s7);
      var s9 := Dup5(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(10) == 0x139;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Dup1(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Dup4(s17);
      var s19 := IsZero(s18);
      var s20 := IsZero(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(14) == 0x139;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x20);
      var s24 := Add(s23);
      var s25 := Dup3(s24);
      var s26 := Dup2(s25);
      var s27 := Sub(s26);
      var s28 := Dup3(s27);
      var s29 := MStore(s28);
      var s30 := Dup6(s29);
      var s31 := Dup6(s30);
      assert s31.Peek(14) == 0x139;
      var s32 := Dup3(s31);
      var s33 := Dup2(s32);
      var s34 := Dup2(s33);
      var s35 := MStore(s34);
      var s36 := Push1(s35, 0x20);
      var s37 := Add(s36);
      var s38 := Swap3(s37);
      var s39 := Pop(s38);
      var s40 := Dup1(s39);
      var s41 := Dup3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s215(s41, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 70
    * Starting at 0x3c3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[16] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      assert s1.Peek(17) == 0x139;
      var s2 := CallDataCopy(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup2(s3);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x1f);
      var s9 := Not(s8);
      var s10 := Push1(s9, 0x1f);
      var s11 := Dup3(s10);
      assert s11.Peek(17) == 0x139;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup1(s15);
      var s17 := Dup4(s16);
      var s18 := Add(s17);
      var s19 := Swap3(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(13) == 0x139;
      var s22 := Pop(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Push1(s28, 0x40);
      var s30 := MLoad(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(9) == 0x139;
      var s32 := Dup2(s31);
      var s33 := Dup4(s32);
      var s34 := Sub(s33);
      var s35 := Sub(s34);
      var s36 := Dup2(s35);
      var s37 := MStore(s36);
      var s38 := Swap1(s37);
      var s39 := Push1(s38, 0x40);
      var s40 := MStore(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s216(s41, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 71
    * Starting at 0x3f2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MLoad(s0);
      assert s1.Peek(8) == 0x139;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Add(s3);
      var s5 := Keccak256(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup9(s10);
      assert s11.Peek(10) == 0x139;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := And(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0xa0);
      var s21 := Shl(s20);
      assert s21.Peek(12) == 0x139;
      var s22 := Sub(s21);
      var s23 := And(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(9) == 0x139;
      var s32 := Add(s31);
      var s33 := Push1(s32, 0x00);
      var s34 := Keccak256(s33);
      var s35 := SLoad(s34);
      var s36 := Eq(s35);
      var s37 := Push2(s36, 0x046f);
      var s38 := JumpI(s37);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s37.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s38, gas - 1)
      else
        ExecuteFromCFGNode_s217(s38, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 72
    * Starting at 0x426
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x426 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(7) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(11) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x1a);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 26, 0x494d504c454d454e544154494f4e5f4e4f545f50454e44494e47);
      var s20 := Push1(s19, 0x30);
      var s21 := Shl(s20);
      assert s21.Peek(9) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(8) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 218
    * Segment Id for this node is: 73
    * Starting at 0x46f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x139;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup7(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x02);
      var s7 := Push1(s6, 0x20);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(7) == 0x139;
      var s12 := SLoad(s11);
      var s13 := Dup7(s12);
      var s14 := Swap1(s13);
      var s15 := Dup1(s14);
      var s16 := Push2(s15, 0x04cf);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s220(s17, gas - 1)
      else
        ExecuteFromCFGNode_s219(s17, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 74
    * Starting at 0x486
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x486 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(13) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x1a);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 26, 0x494d504c454d454e544154494f4e5f4e4f545f50454e44494e47);
      var s20 := Push1(s19, 0x30);
      var s21 := Shl(s20);
      assert s21.Peek(11) == 0x139;
      var s22 := Push1(s21, 0x44);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Swap1(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(10) == 0x139;
      var s32 := Push1(s31, 0x64);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Revert(s34);
      // Segment is terminal (Revert, Stop or Return)
      s35
  }

  /** Node 220
    * Segment Id for this node is: 75
    * Starting at 0x4cf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x139;
      var s2 := TimeStamp(s1);
      var s3 := Push3(s2, 0xed4e00);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x0528);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s222(s8, gas - 1)
      else
        ExecuteFromCFGNode_s221(s8, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 76
    * Starting at 0x4dc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0x139;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(13) == 0x139;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x1f);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x494e56414c49445f50454e44494e475f41435449564154494f4e5f54494d4500);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(13) == 0x139;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Swap1(s23);
      var s25 := MLoad(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Swap1(s27);
      var s29 := Sub(s28);
      var s30 := Push1(s29, 0x64);
      var s31 := Add(s30);
      assert s31.Peek(10) == 0x139;
      var s32 := Swap1(s31);
      var s33 := Revert(s32);
      // Segment is terminal (Revert, Stop or Return)
      s33
  }

  /** Node 222
    * Segment Id for this node is: 77
    * Starting at 0x528
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x528 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x139;
      var s2 := Dup1(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0581);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s224(s7, gas - 1)
      else
        ExecuteFromCFGNode_s223(s7, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 78
    * Starting at 0x531
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x531 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(9) == 0x139;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x02);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap2(s10);
      assert s11.Peek(11) == 0x139;
      var s12 := Dup3(s11);
      var s13 := Swap1(s12);
      var s14 := Keccak256(s13);
      var s15 := Dup7(s14);
      var s16 := Swap1(s15);
      var s17 := SStore(s16);
      var s18 := Dup2(s17);
      var s19 := MLoad(s18);
      var s20 := Dup7(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(13) == 0x139;
      var s22 := MStore(s21);
      var s23 := Swap2(s22);
      var s24 := MLoad(s23);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0xa0);
      var s28 := Shl(s27);
      var s29 := Sub(s28);
      var s30 := Dup12(s29);
      var s31 := And(s30);
      assert s31.Peek(12) == 0x139;
      var s32 := Swap3(s31);
      var s33 := Push32(s32, 0xdda7b7d1f8141bd98b4378ee60e6231f89598ca02949a9d0550904dc96efeeb7);
      var s34 := Swap3(s33);
      var s35 := Swap1(s34);
      var s36 := Dup3(s35);
      var s37 := Swap1(s36);
      var s38 := Sub(s37);
      var s39 := Add(s38);
      var s40 := Swap1(s39);
      var s41 := Log2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s224(s41, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 79
    * Starting at 0x581
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x581 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x139

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x139;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s10, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 17
    * Starting at 0xb4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4 as nat
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
