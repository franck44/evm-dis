
include "/Users/franck/development/evm-dis/src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module EVMProofObject {

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
      var s1 := PushN(s0, 1, 0x04);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x000d);
      assert s5.stack[0] == 0xd;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s3(s6, gas - 1)
      else
        ExecuteFromCFGNode_s1(s6, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0x9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x133c);
      assert s1.stack[0] == 0x133c;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s2(s2, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 262
    * Starting at 0x133c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x133c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 3
    * Segment Id for this node is: 2
    * Starting at 0xd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 1, 0x1c);
      var s5 := CallDataCopy(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := MLoad(s6);
      var s8 := CallValue(s7);
      var s9 := PushN(s8, 2, 0x1342);
      assert s9.stack[0] == 0x1342;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s10, gas - 1)
      else
        ExecuteFromCFGNode_s4(s10, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 3
    * Starting at 0x1d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 4, 0x84738499);
      var s2 := Dup(s1, 2);
      var s3 := Xor(s2);
      var s4 := PushN(s3, 2, 0x0030);
      assert s4.stack[0] == 0x30;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 4
    * Starting at 0x28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x004a);
      assert s4.stack[0] == 0x4a;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 8
    * Starting at 0x4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
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
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := CallDataSize(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := CallDataCopy(s4);
      var s6 := PushN(s5, 2, 0x01e0);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 1, 0x03);
      var s9 := Dup(s8, 2);
      var s10 := Dup(s9, 4);
      var s11 := MStore(s10);
      var s12 := Add(s11);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s7(s12, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 9
    * Starting at 0x5d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x01e0);
      var s4 := MLoad(s3);
      var s5 := Mul(s4);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := PushN(s8, 2, 0x0200);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x00);
      var s12 := PushN(s11, 2, 0x0200);
      var s13 := MLoad(s12);
      var s14 := Eq(s13);
      var s15 := PushN(s14, 2, 0x01e6);
      assert s15.stack[0] == 0x1e6;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s16, gas - 1)
      else
        ExecuteFromCFGNode_s8(s16, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 10
    * Starting at 0x78
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x01);
      var s2 := PushN(s1, 2, 0x01e0);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x05);
      var s5 := Dup(s4, 2);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x1342);
      assert s8.stack[0] == 0x1342;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s9, gas - 1)
      else
        ExecuteFromCFGNode_s9(s9, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 11
    * Starting at 0x87
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x03);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 2, 0x0220);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 1, 0x04);
      var s9 := PushN(s8, 2, 0x0280);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 32, 0x23b872dd00000000000000000000000000000000000000000000000000000000);
      var s12 := PushN(s11, 2, 0x02a0);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 2, 0x0280);
      var s15 := PushN(s14, 1, 0x04);
      var s16 := Dup(s15, 1);
      var s17 := PushN(s16, 1, 0x20);
      var s18 := Dup(s17, 5);
      var s19 := PushN(s18, 2, 0x02c0);
      var s20 := Add(s19);
      var s21 := Add(s20);
      var s22 := Dup(s21, 3);
      var s23 := PushN(s22, 1, 0x20);
      var s24 := Dup(s23, 6);
      var s25 := Add(s24);
      var s26 := PushN(s25, 1, 0x04);
      var s27 := Gas(s26);
      var s28 := StaticCall(s27);
      var s29 := Pop(s28);
      var s30 := Pop(s29);
      var s31 := Dup(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s10(s31, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 12
    * Starting at 0xd7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MLoad(s0);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 2);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Caller(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := Dup(s8, 3);
      var s10 := PushN(s9, 2, 0x02c0);
      var s11 := Add(s10);
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 1, 0x20);
      var s15 := Dup(s14, 2);
      var s16 := Add(s15);
      var s17 := Swap(s16, 1);
      var s18 := Pop(s17);
      var s19 := Address(s18);
      var s20 := PushN(s19, 1, 0x20);
      var s21 := Dup(s20, 3);
      var s22 := PushN(s21, 2, 0x02c0);
      var s23 := Add(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := PushN(s25, 1, 0x20);
      var s27 := Dup(s26, 2);
      var s28 := Add(s27);
      var s29 := Swap(s28, 1);
      var s30 := Pop(s29);
      var s31 := PushN(s30, 2, 0x0200);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s11(s31, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 13
    * Starting at 0x100
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MLoad(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := Dup(s2, 3);
      var s4 := PushN(s3, 2, 0x02c0);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := Dup(s8, 2);
      var s10 := Add(s9);
      var s11 := Swap(s10, 1);
      var s12 := Pop(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x02c0);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 2, 0x02c0);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := PushN(s18, 1, 0x20);
      var s20 := PushN(s19, 2, 0x0380);
      var s21 := PushN(s20, 2, 0x02c0);
      var s22 := MLoad(s21);
      var s23 := PushN(s22, 2, 0x02e0);
      var s24 := PushN(s23, 1, 0x00);
      var s25 := PushN(s24, 2, 0x0220);
      var s26 := MLoad(s25);
      var s27 := Gas(s26);
      var s28 := Call(s27);
      var s29 := PushN(s28, 2, 0x013c);
      assert s29.stack[0] == 0x13c;
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s13(s30, gas - 1)
      else
        ExecuteFromCFGNode_s12(s30, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 14
    * Starting at 0x132
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 13
    * Segment Id for this node is: 15
    * Starting at 0x13c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0360);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Gt(s6);
      var s8 := PushN(s7, 2, 0x014f);
      assert s8.stack[0] == 0x14f;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s9, gas - 1)
      else
        ExecuteFromCFGNode_s14(s9, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 16
    * Starting at 0x14a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x0151);
      assert s2.stack[0] == 0x151;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s3, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 18
    * Starting at 0x151
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Add(s10);
      var s12 := Dup(s11, 1);
      var s13 := PushN(s12, 2, 0x0240);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := PushN(s15, 1, 0x04);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0240);
      var s25 := MLoad(s24);
      var s26 := Eq(s25);
      var s27 := PushN(s26, 2, 0x0190);
      assert s27.stack[0] == 0x190;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s28, gas - 1)
      else
        ExecuteFromCFGNode_s16(s28, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 19
    * Starting at 0x176
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x176 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0260);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0240);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Sub(s7);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := Mul(s9);
      var s11 := Shr(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x1342);
      assert s17.stack[0] == 0x1342;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s18, gas - 1)
      else
        ExecuteFromCFGNode_s17(s18, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 20
    * Starting at 0x190
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x190 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x70a08231);
      var s3 := PushN(s2, 2, 0x0280);
      var s4 := MStore(s3);
      var s5 := Address(s4);
      var s6 := PushN(s5, 2, 0x02a0);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := PushN(s8, 2, 0x0280);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := PushN(s10, 2, 0x029c);
      var s12 := PushN(s11, 2, 0x0220);
      var s13 := MLoad(s12);
      var s14 := Gas(s13);
      var s15 := StaticCall(s14);
      var s16 := PushN(s15, 2, 0x01bd);
      assert s16.stack[0] == 0x1bd;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s17, gas - 1)
      else
        ExecuteFromCFGNode_s18(s17, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 21
    * Starting at 0x1b3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 19
    * Segment Id for this node is: 22
    * Starting at 0x1bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s7, gas - 1)
      else
        ExecuteFromCFGNode_s20(s7, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 23
    * Starting at 0x1c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0280);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0100);
      var s4 := PushN(s3, 2, 0x01e0);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 1, 0x03);
      var s7 := Dup(s6, 2);
      var s8 := Lt(s7);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1342);
      assert s10.stack[0] == 0x1342;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s11, gas - 1)
      else
        ExecuteFromCFGNode_s21(s11, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 24
    * Starting at 0x1db
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := Mul(s1);
      var s3 := Add(s2);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x01);
      var s6 := PushN(s5, 2, 0x01c0);
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s22(s7, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 25
    * Starting at 0x1e6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x01);
      var s5 := Add(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 4);
      var s8 := MStore(s7);
      var s9 := Dup(s8, 2);
      var s10 := Eq(s9);
      var s11 := IsZero(s10);
      var s12 := PushN(s11, 2, 0x005d);
      assert s12.stack[0] == 0x5d;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s7(s13, gas - 1)
      else
        ExecuteFromCFGNode_s23(s13, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 26
    * Starting at 0x1f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x01c0);
      var s4 := MLoad(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x0259);
      assert s6.stack[0] == 0x259;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s7, gas - 1)
      else
        ExecuteFromCFGNode_s24(s7, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 27
    * Starting at 0x201
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x201 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 4, 0x4515cef3);
      var s2 := PushN(s1, 2, 0x01e0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 2, 0x0200);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x0120);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x0220);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x0140);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 2, 0x0240);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 1, 0x00);
      var s17 := PushN(s16, 2, 0x0260);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 1, 0x20);
      var s20 := PushN(s19, 2, 0x01e0);
      var s21 := PushN(s20, 1, 0x84);
      var s22 := PushN(s21, 2, 0x01fc);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 1, 0x09);
      var s25 := SLoad(s24);
      var s26 := Gas(s25);
      var s27 := Call(s26);
      var s28 := PushN(s27, 2, 0x0247);
      assert s28.stack[0] == 0x247;
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s26(s29, gas - 1)
      else
        ExecuteFromCFGNode_s25(s29, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 28
    * Starting at 0x23d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 26
    * Segment Id for this node is: 29
    * Starting at 0x247
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x247 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s27(s7, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 30
    * Starting at 0x251
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x251 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01e0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s28(s4, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 31
    * Starting at 0x259
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x259 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x01e0);
      var s3 := PushN(s2, 1, 0x03);
      var s4 := PushN(s3, 1, 0x02);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 4);
      var s7 := MStore(s6);
      var s8 := Add(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s29(s8, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 32
    * Starting at 0x265
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x265 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x01e0);
      var s4 := MLoad(s3);
      var s5 := Mul(s4);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := PushN(s8, 2, 0x0200);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x00);
      var s12 := PushN(s11, 2, 0x0200);
      var s13 := MLoad(s12);
      var s14 := Eq(s13);
      var s15 := PushN(s14, 2, 0x03c2);
      assert s15.stack[0] == 0x3c2;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s16, gas - 1)
      else
        ExecuteFromCFGNode_s30(s16, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 33
    * Starting at 0x280
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x280 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x01);
      var s2 := PushN(s1, 2, 0x01e0);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x05);
      var s5 := Dup(s4, 2);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x1342);
      assert s8.stack[0] == 0x1342;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s9, gas - 1)
      else
        ExecuteFromCFGNode_s31(s9, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 34
    * Starting at 0x28f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x03);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 2, 0x0220);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 1, 0x04);
      var s9 := PushN(s8, 2, 0x0280);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 32, 0x23b872dd00000000000000000000000000000000000000000000000000000000);
      var s12 := PushN(s11, 2, 0x02a0);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 2, 0x0280);
      var s15 := PushN(s14, 1, 0x04);
      var s16 := Dup(s15, 1);
      var s17 := PushN(s16, 1, 0x20);
      var s18 := Dup(s17, 5);
      var s19 := PushN(s18, 2, 0x02c0);
      var s20 := Add(s19);
      var s21 := Add(s20);
      var s22 := Dup(s21, 3);
      var s23 := PushN(s22, 1, 0x20);
      var s24 := Dup(s23, 6);
      var s25 := Add(s24);
      var s26 := PushN(s25, 1, 0x04);
      var s27 := Gas(s26);
      var s28 := StaticCall(s27);
      var s29 := Pop(s28);
      var s30 := Pop(s29);
      var s31 := Dup(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s32(s31, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 35
    * Starting at 0x2df
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MLoad(s0);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 2);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Caller(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := Dup(s8, 3);
      var s10 := PushN(s9, 2, 0x02c0);
      var s11 := Add(s10);
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 1, 0x20);
      var s15 := Dup(s14, 2);
      var s16 := Add(s15);
      var s17 := Swap(s16, 1);
      var s18 := Pop(s17);
      var s19 := Address(s18);
      var s20 := PushN(s19, 1, 0x20);
      var s21 := Dup(s20, 3);
      var s22 := PushN(s21, 2, 0x02c0);
      var s23 := Add(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := PushN(s25, 1, 0x20);
      var s27 := Dup(s26, 2);
      var s28 := Add(s27);
      var s29 := Swap(s28, 1);
      var s30 := Pop(s29);
      var s31 := PushN(s30, 2, 0x0200);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s33(s31, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 36
    * Starting at 0x308
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x308 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MLoad(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := Dup(s2, 3);
      var s4 := PushN(s3, 2, 0x02c0);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := Dup(s8, 2);
      var s10 := Add(s9);
      var s11 := Swap(s10, 1);
      var s12 := Pop(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x02c0);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 2, 0x02c0);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := PushN(s18, 1, 0x20);
      var s20 := PushN(s19, 2, 0x0380);
      var s21 := PushN(s20, 2, 0x02c0);
      var s22 := MLoad(s21);
      var s23 := PushN(s22, 2, 0x02e0);
      var s24 := PushN(s23, 1, 0x00);
      var s25 := PushN(s24, 2, 0x0220);
      var s26 := MLoad(s25);
      var s27 := Gas(s26);
      var s28 := Call(s27);
      var s29 := PushN(s28, 2, 0x0344);
      assert s29.stack[0] == 0x344;
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s30, gas - 1)
      else
        ExecuteFromCFGNode_s34(s30, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 37
    * Starting at 0x33a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 35
    * Segment Id for this node is: 38
    * Starting at 0x344
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x344 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0360);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Gt(s6);
      var s8 := PushN(s7, 2, 0x0357);
      assert s8.stack[0] == 0x357;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s9, gas - 1)
      else
        ExecuteFromCFGNode_s36(s9, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 39
    * Starting at 0x352
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x352 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x0359);
      assert s2.stack[0] == 0x359;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s3, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 41
    * Starting at 0x359
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x359 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Add(s10);
      var s12 := Dup(s11, 1);
      var s13 := PushN(s12, 2, 0x0240);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := PushN(s15, 1, 0x04);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0240);
      var s25 := MLoad(s24);
      var s26 := Eq(s25);
      var s27 := PushN(s26, 2, 0x0398);
      assert s27.stack[0] == 0x398;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s28, gas - 1)
      else
        ExecuteFromCFGNode_s38(s28, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 42
    * Starting at 0x37e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0260);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0240);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Sub(s7);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := Mul(s9);
      var s11 := Shr(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x1342);
      assert s17.stack[0] == 0x1342;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s18, gas - 1)
      else
        ExecuteFromCFGNode_s39(s18, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 43
    * Starting at 0x398
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x398 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0200);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0160);
      var s5 := PushN(s4, 2, 0x01e0);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 1, 0x02);
      var s8 := Dup(s7, 1);
      var s9 := Dup(s8, 3);
      var s10 := Lt(s9);
      var s11 := PushN(s10, 2, 0x1342);
      assert s11.stack[0] == 0x1342;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s12, gas - 1)
      else
        ExecuteFromCFGNode_s40(s12, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 44
    * Starting at 0x3ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Sub(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 1, 0x03);
      var s9 := Dup(s8, 2);
      var s10 := Lt(s9);
      var s11 := IsZero(s10);
      var s12 := PushN(s11, 2, 0x1342);
      assert s12.stack[0] == 0x1342;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s13, gas - 1)
      else
        ExecuteFromCFGNode_s41(s13, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 45
    * Starting at 0x3bd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := Mul(s1);
      var s3 := Add(s2);
      var s4 := MStore(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s42(s4, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 46
    * Starting at 0x3c2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x01);
      var s5 := Add(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 4);
      var s8 := MStore(s7);
      var s9 := Dup(s8, 2);
      var s10 := Eq(s9);
      var s11 := IsZero(s10);
      var s12 := PushN(s11, 2, 0x0265);
      assert s12.stack[0] == 0x265;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s13, gas - 1)
      else
        ExecuteFromCFGNode_s43(s13, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 47
    * Starting at 0x3d2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 4, 0x4515cef3);
      var s4 := PushN(s3, 2, 0x01e0);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MLoad(s6);
      var s8 := PushN(s7, 2, 0x0200);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x0180);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 2, 0x0220);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 2, 0x01a0);
      var s15 := MLoad(s14);
      var s16 := PushN(s15, 2, 0x0240);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 1, 0xa4);
      var s19 := CallDataLoad(s18);
      var s20 := PushN(s19, 2, 0x0260);
      var s21 := MStore(s20);
      var s22 := PushN(s21, 1, 0x08);
      var s23 := SLoad(s22);
      var s24 := ExtCodeSize(s23);
      var s25 := IsZero(s24);
      var s26 := PushN(s25, 2, 0x1342);
      assert s26.stack[0] == 0x1342;
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s27, gas - 1)
      else
        ExecuteFromCFGNode_s44(s27, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 48
    * Starting at 0x405
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x405 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x84);
      var s4 := PushN(s3, 2, 0x01fc);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 1, 0x08);
      var s7 := SLoad(s6);
      var s8 := Gas(s7);
      var s9 := Call(s8);
      var s10 := PushN(s9, 2, 0x0423);
      assert s10.stack[0] == 0x423;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s46(s11, gas - 1)
      else
        ExecuteFromCFGNode_s45(s11, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 49
    * Starting at 0x419
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x419 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 46
    * Segment Id for this node is: 50
    * Starting at 0x423
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x423 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x0a);
      var s3 := SLoad(s2);
      var s4 := PushN(s3, 2, 0x01e0);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 4, 0x70a08231);
      var s7 := PushN(s6, 2, 0x0220);
      var s8 := MStore(s7);
      var s9 := Address(s8);
      var s10 := PushN(s9, 2, 0x0240);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := PushN(s12, 2, 0x0220);
      var s14 := PushN(s13, 1, 0x24);
      var s15 := PushN(s14, 2, 0x023c);
      var s16 := PushN(s15, 2, 0x01e0);
      var s17 := MLoad(s16);
      var s18 := Gas(s17);
      var s19 := StaticCall(s18);
      var s20 := PushN(s19, 2, 0x0457);
      assert s20.stack[0] == 0x457;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s21, gas - 1)
      else
        ExecuteFromCFGNode_s47(s21, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 51
    * Starting at 0x44d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 48
    * Segment Id for this node is: 52
    * Starting at 0x457
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s49(s7, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 53
    * Starting at 0x461
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x461 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0220);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0200);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 4, 0xa9059cbb);
      var s6 := PushN(s5, 2, 0x0220);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0xe0);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x0240);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x0200);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 2, 0x0260);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 1, 0x20);
      var s17 := PushN(s16, 2, 0x0220);
      var s18 := PushN(s17, 1, 0x44);
      var s19 := PushN(s18, 2, 0x023c);
      var s20 := PushN(s19, 1, 0x00);
      var s21 := PushN(s20, 2, 0x01e0);
      var s22 := MLoad(s21);
      var s23 := Gas(s22);
      var s24 := Call(s23);
      var s25 := PushN(s24, 2, 0x04a1);
      assert s25.stack[0] == 0x4a1;
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s26, gas - 1)
      else
        ExecuteFromCFGNode_s50(s26, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 54
    * Starting at 0x497
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x497 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 51
    * Segment Id for this node is: 55
    * Starting at 0x4a1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s52(s7, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 56
    * Starting at 0x4ab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0220);
      var s2 := Pop(s1);
      var s3 := Stop(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 53
    * Segment Id for this node is: 263
    * Starting at 0x1342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 54
    * Segment Id for this node is: 263
    * Starting at 0x1342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 55
    * Segment Id for this node is: 263
    * Starting at 0x1342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 56
    * Segment Id for this node is: 263
    * Starting at 0x1342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 57
    * Segment Id for this node is: 40
    * Starting at 0x357
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s37(s2, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 263
    * Starting at 0x1342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 59
    * Segment Id for this node is: 17
    * Starting at 0x14f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s15(s2, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 5
    * Starting at 0x30
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xcf2b51b8);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x04b0);
      assert s5.stack[0] == 0x4b0;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s6, gas - 1)
      else
        ExecuteFromCFGNode_s61(s6, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 6
    * Starting at 0x3c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xc4);
      var s2 := CallDataLoad(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 1, 0xa0);
      var s5 := Shr(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s7, gas - 1)
      else
        ExecuteFromCFGNode_s62(s7, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 7
    * Starting at 0x47
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MStore(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s6(s2, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 263
    * Starting at 0x1342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 64
    * Segment Id for this node is: 57
    * Starting at 0x4b0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x65b2489b);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x04c4);
      assert s5.stack[0] == 0x4c4;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s120(s6, gas - 1)
      else
        ExecuteFromCFGNode_s65(s6, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 58
    * Starting at 0x4bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x04de);
      assert s4.stack[0] == 0x4de;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s5, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 62
    * Starting at 0x4de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := PushN(s3, 2, 0x0140);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 32, 0x23b872dd00000000000000000000000000000000000000000000000000000000);
      var s7 := PushN(s6, 2, 0x0160);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0140);
      var s10 := PushN(s9, 1, 0x04);
      var s11 := Dup(s10, 1);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Dup(s12, 5);
      var s14 := PushN(s13, 2, 0x0180);
      var s15 := Add(s14);
      var s16 := Add(s15);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 6);
      var s20 := Add(s19);
      var s21 := PushN(s20, 1, 0x04);
      var s22 := Gas(s21);
      var s23 := StaticCall(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Dup(s25, 1);
      var s27 := MLoad(s26);
      var s28 := Dup(s27, 3);
      var s29 := Add(s28);
      var s30 := Swap(s29, 2);
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s67(s31, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 63
    * Starting at 0x52b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Caller(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := Dup(s3, 3);
      var s5 := PushN(s4, 2, 0x0180);
      var s6 := Add(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x20);
      var s10 := Dup(s9, 2);
      var s11 := Add(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Address(s13);
      var s15 := PushN(s14, 1, 0x20);
      var s16 := Dup(s15, 3);
      var s17 := PushN(s16, 2, 0x0180);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := PushN(s20, 1, 0x20);
      var s22 := Dup(s21, 2);
      var s23 := Add(s22);
      var s24 := Swap(s23, 1);
      var s25 := Pop(s24);
      var s26 := PushN(s25, 1, 0x44);
      var s27 := CallDataLoad(s26);
      var s28 := PushN(s27, 1, 0x20);
      var s29 := Dup(s28, 3);
      var s30 := PushN(s29, 2, 0x0180);
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s68(s31, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 64
    * Starting at 0x556
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x556 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := Dup(s3, 2);
      var s5 := Add(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := Dup(s7, 1);
      var s9 := PushN(s8, 2, 0x0180);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0180);
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := PushN(s13, 1, 0x20);
      var s15 := PushN(s14, 2, 0x0240);
      var s16 := PushN(s15, 2, 0x0180);
      var s17 := MLoad(s16);
      var s18 := PushN(s17, 2, 0x01a0);
      var s19 := PushN(s18, 1, 0x00);
      var s20 := PushN(s19, 1, 0x01);
      var s21 := PushN(s20, 1, 0x04);
      var s22 := CallDataLoad(s21);
      var s23 := PushN(s22, 1, 0x05);
      var s24 := Dup(s23, 2);
      var s25 := Lt(s24);
      var s26 := IsZero(s25);
      var s27 := PushN(s26, 2, 0x1342);
      assert s27.stack[0] == 0x1342;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s28, gas - 1)
      else
        ExecuteFromCFGNode_s69(s28, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 65
    * Starting at 0x584
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x584 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x03);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := PushN(s6, 2, 0x0599);
      assert s7.stack[0] == 0x599;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s8, gas - 1)
      else
        ExecuteFromCFGNode_s70(s8, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 66
    * Starting at 0x58f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 71
    * Segment Id for this node is: 67
    * Starting at 0x599
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x599 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0220);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Gt(s6);
      var s8 := PushN(s7, 2, 0x05ac);
      assert s8.stack[0] == 0x5ac;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s119(s9, gas - 1)
      else
        ExecuteFromCFGNode_s72(s9, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 68
    * Starting at 0x5a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x05ae);
      assert s2.stack[0] == 0x5ae;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s3, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 70
    * Starting at 0x5ae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Add(s10);
      var s12 := Dup(s11, 1);
      var s13 := PushN(s12, 2, 0x0100);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := PushN(s15, 1, 0x04);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0100);
      var s25 := MLoad(s24);
      var s26 := Eq(s25);
      var s27 := PushN(s26, 2, 0x05ed);
      assert s27.stack[0] == 0x5ed;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s28, gas - 1)
      else
        ExecuteFromCFGNode_s74(s28, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 71
    * Starting at 0x5d3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0120);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0100);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Sub(s7);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := Mul(s9);
      var s11 := Shr(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x1342);
      assert s17.stack[0] == 0x1342;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s18, gas - 1)
      else
        ExecuteFromCFGNode_s75(s18, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 72
    * Starting at 0x5ed
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x44);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 2, 0x0140);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x40);
      var s7 := CallDataSize(s6);
      var s8 := PushN(s7, 2, 0x0160);
      var s9 := CallDataCopy(s8);
      var s10 := PushN(s9, 1, 0x03);
      var s11 := PushN(s10, 1, 0x24);
      var s12 := CallDataLoad(s11);
      var s13 := Lt(s12);
      var s14 := PushN(s13, 2, 0x061d);
      assert s14.stack[0] == 0x61d;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s15, gas - 1)
      else
        ExecuteFromCFGNode_s76(s15, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 73
    * Starting at 0x606
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x606 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x24);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0x02);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := Lt(s5);
      var s7 := PushN(s6, 2, 0x1342);
      assert s7.stack[0] == 0x1342;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s8, gas - 1)
      else
        ExecuteFromCFGNode_s77(s8, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 74
    * Starting at 0x612
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x612 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Sub(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0180);
      var s9 := MStore(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s78(s9, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 75
    * Starting at 0x61d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x03);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := CallDataLoad(s3);
      var s5 := Lt(s4);
      var s6 := PushN(s5, 2, 0x0643);
      assert s6.stack[0] == 0x643;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s112(s7, gas - 1)
      else
        ExecuteFromCFGNode_s79(s7, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 76
    * Starting at 0x628
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x628 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0x02);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := Lt(s5);
      var s7 := PushN(s6, 2, 0x1342);
      assert s7.stack[0] == 0x1342;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s8, gas - 1)
      else
        ExecuteFromCFGNode_s80(s8, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 77
    * Starting at 0x634
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x634 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Sub(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0160);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x06bb);
      assert s10.stack[0] == 0x6bb;
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s11, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 84
    * Starting at 0x6bb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0180);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 3);
      var s9 := Lt(s8);
      var s10 := PushN(s9, 2, 0x06d2);
      assert s10.stack[0] == 0x6d2;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s11, gas - 1)
      else
        ExecuteFromCFGNode_s82(s11, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 85
    * Starting at 0x6cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x06d4);
      assert s2.stack[0] == 0x6d4;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s3, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 87
    * Starting at 0x6d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x072d);
      assert s8.stack[0] == 0x72d;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s9, gas - 1)
      else
        ExecuteFromCFGNode_s84(s9, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 88
    * Starting at 0x6df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 4, 0x5b41b908);
      var s2 := PushN(s1, 2, 0x01a0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x0160);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 2, 0x01c0);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x0180);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x01e0);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x0140);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 2, 0x0200);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 1, 0x00);
      var s17 := PushN(s16, 2, 0x0220);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 1, 0x08);
      var s20 := SLoad(s19);
      var s21 := ExtCodeSize(s20);
      var s22 := IsZero(s21);
      var s23 := PushN(s22, 2, 0x1342);
      assert s23.stack[0] == 0x1342;
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s24, gas - 1)
      else
        ExecuteFromCFGNode_s85(s24, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 89
    * Starting at 0x70f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x84);
      var s4 := PushN(s3, 2, 0x01bc);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 1, 0x08);
      var s7 := SLoad(s6);
      var s8 := Gas(s7);
      var s9 := Call(s8);
      var s10 := PushN(s9, 2, 0x072d);
      assert s10.stack[0] == 0x72d;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s11, gas - 1)
      else
        ExecuteFromCFGNode_s86(s11, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 90
    * Starting at 0x723
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 87
    * Segment Id for this node is: 91
    * Starting at 0x72d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x70a08231);
      var s3 := PushN(s2, 2, 0x01c0);
      var s4 := MStore(s3);
      var s5 := Address(s4);
      var s6 := PushN(s5, 2, 0x01e0);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := PushN(s8, 2, 0x01c0);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := PushN(s10, 2, 0x01dc);
      var s12 := PushN(s11, 1, 0x01);
      var s13 := PushN(s12, 2, 0x0180);
      var s14 := MLoad(s13);
      var s15 := PushN(s14, 1, 0x03);
      var s16 := Dup(s15, 2);
      var s17 := Lt(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x1342);
      assert s19.stack[0] == 0x1342;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s20, gas - 1)
      else
        ExecuteFromCFGNode_s88(s20, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 92
    * Starting at 0x755
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x755 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := SLoad(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := PushN(s4, 2, 0x0767);
      assert s5.stack[0] == 0x767;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s6, gas - 1)
      else
        ExecuteFromCFGNode_s89(s6, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 93
    * Starting at 0x75d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 90
    * Segment Id for this node is: 94
    * Starting at 0x767
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x767 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s91(s7, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 95
    * Starting at 0x771
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x771 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01c0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x01a0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x0180);
      var s6 := MLoad(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x0792);
      assert s8.stack[0] == 0x792;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s9, gas - 1)
      else
        ExecuteFromCFGNode_s92(s9, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 96
    * Starting at 0x782
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x782 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x64);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 2, 0x01a0);
      var s4 := MLoad(s3);
      var s5 := Lt(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s93(s7, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 97
    * Starting at 0x78e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x07eb);
      assert s1.stack[0] == 0x7eb;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s2, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 103
    * Starting at 0x7eb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := PushN(s3, 2, 0x01c0);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 32, 0xa9059cbb00000000000000000000000000000000000000000000000000000000);
      var s7 := PushN(s6, 2, 0x01e0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x01c0);
      var s10 := PushN(s9, 1, 0x04);
      var s11 := Dup(s10, 1);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Dup(s12, 5);
      var s14 := PushN(s13, 2, 0x0200);
      var s15 := Add(s14);
      var s16 := Add(s15);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 6);
      var s20 := Add(s19);
      var s21 := PushN(s20, 1, 0x04);
      var s22 := Gas(s21);
      var s23 := StaticCall(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Dup(s25, 1);
      var s27 := MLoad(s26);
      var s28 := Dup(s27, 3);
      var s29 := Add(s28);
      var s30 := Swap(s29, 2);
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s95(s31, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 104
    * Starting at 0x838
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x838 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x20);
      var s5 := Dup(s4, 3);
      var s6 := PushN(s5, 2, 0x0200);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Dup(s10, 2);
      var s12 := Add(s11);
      var s13 := Swap(s12, 1);
      var s14 := Pop(s13);
      var s15 := PushN(s14, 2, 0x01a0);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 1, 0x20);
      var s18 := Dup(s17, 3);
      var s19 := PushN(s18, 2, 0x0200);
      var s20 := Add(s19);
      var s21 := Add(s20);
      var s22 := MStore(s21);
      var s23 := PushN(s22, 1, 0x20);
      var s24 := Dup(s23, 2);
      var s25 := Add(s24);
      var s26 := Swap(s25, 1);
      var s27 := Pop(s26);
      var s28 := Dup(s27, 1);
      var s29 := PushN(s28, 2, 0x0200);
      var s30 := MStore(s29);
      var s31 := PushN(s30, 2, 0x0200);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s96(s31, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 105
    * Starting at 0x866
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x866 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x02a0);
      var s5 := PushN(s4, 2, 0x0200);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0220);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 1, 0x01);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 1, 0x05);
      var s13 := Dup(s12, 2);
      var s14 := Lt(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x1342);
      assert s16.stack[0] == 0x1342;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s17, gas - 1)
      else
        ExecuteFromCFGNode_s97(s17, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 106
    * Starting at 0x884
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x884 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x03);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := PushN(s6, 2, 0x0899);
      assert s7.stack[0] == 0x899;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s99(s8, gas - 1)
      else
        ExecuteFromCFGNode_s98(s8, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 107
    * Starting at 0x88f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 99
    * Segment Id for this node is: 108
    * Starting at 0x899
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x899 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0280);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Gt(s6);
      var s8 := PushN(s7, 2, 0x08ac);
      assert s8.stack[0] == 0x8ac;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s104(s9, gas - 1)
      else
        ExecuteFromCFGNode_s100(s9, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 109
    * Starting at 0x8a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x08ae);
      assert s2.stack[0] == 0x8ae;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s3, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 111
    * Starting at 0x8ae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Add(s10);
      var s12 := Dup(s11, 1);
      var s13 := PushN(s12, 2, 0x0100);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := PushN(s15, 1, 0x04);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0100);
      var s25 := MLoad(s24);
      var s26 := Eq(s25);
      var s27 := PushN(s26, 2, 0x08ed);
      assert s27.stack[0] == 0x8ed;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s28, gas - 1)
      else
        ExecuteFromCFGNode_s102(s28, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 112
    * Starting at 0x8d3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0120);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0100);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Sub(s7);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := Mul(s9);
      var s11 := Shr(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x1342);
      assert s17.stack[0] == 0x1342;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s18, gas - 1)
      else
        ExecuteFromCFGNode_s103(s18, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 113
    * Starting at 0x8ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ed as nat
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

  /** Node 104
    * Segment Id for this node is: 110
    * Starting at 0x8ac
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s101(s2, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 263
    * Starting at 0x1342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 106
    * Segment Id for this node is: 98
    * Starting at 0x792
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x792 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x1a4d01d2);
      var s3 := PushN(s2, 2, 0x01c0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x01a0);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x01e0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x24);
      var s10 := CallDataLoad(s9);
      var s11 := Dup(s10, 1);
      var s12 := PushN(s11, 1, 0x7f);
      var s13 := Shr(s12);
      var s14 := PushN(s13, 2, 0x1342);
      assert s14.stack[0] == 0x1342;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s15, gas - 1)
      else
        ExecuteFromCFGNode_s107(s15, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 99
    * Starting at 0x7af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0200);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x64);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 2, 0x0220);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 2, 0x01c0);
      var s9 := PushN(s8, 1, 0x64);
      var s10 := PushN(s9, 2, 0x01dc);
      var s11 := PushN(s10, 1, 0x00);
      var s12 := PushN(s11, 1, 0x09);
      var s13 := SLoad(s12);
      var s14 := Gas(s13);
      var s15 := Call(s14);
      var s16 := PushN(s15, 2, 0x07d9);
      assert s16.stack[0] == 0x7d9;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s109(s17, gas - 1)
      else
        ExecuteFromCFGNode_s108(s17, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 100
    * Starting at 0x7cf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 109
    * Segment Id for this node is: 101
    * Starting at 0x7d9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s110(s7, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 102
    * Starting at 0x7e3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01c0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x01a0);
      var s4 := MStore(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s94(s4, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 86
    * Starting at 0x6d2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s83(s2, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 78
    * Starting at 0x643
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x643 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x60);
      var s3 := CallDataSize(s2);
      var s4 := PushN(s3, 2, 0x01a0);
      var s5 := CallDataCopy(s4);
      var s6 := PushN(s5, 2, 0x0140);
      var s7 := MLoad(s6);
      var s8 := PushN(s7, 2, 0x01a0);
      var s9 := PushN(s8, 1, 0x04);
      var s10 := CallDataLoad(s9);
      var s11 := PushN(s10, 1, 0x03);
      var s12 := Dup(s11, 2);
      var s13 := Lt(s12);
      var s14 := IsZero(s13);
      var s15 := PushN(s14, 2, 0x1342);
      assert s15.stack[0] == 0x1342;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s16, gas - 1)
      else
        ExecuteFromCFGNode_s113(s16, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 79
    * Starting at 0x65e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := Mul(s1);
      var s3 := Add(s2);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 4, 0x4515cef3);
      var s6 := PushN(s5, 2, 0x0200);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x01a0);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x0220);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x01c0);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 2, 0x0240);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 2, 0x01e0);
      var s17 := MLoad(s16);
      var s18 := PushN(s17, 2, 0x0260);
      var s19 := MStore(s18);
      var s20 := PushN(s19, 1, 0x00);
      var s21 := PushN(s20, 2, 0x0280);
      var s22 := MStore(s21);
      var s23 := PushN(s22, 1, 0x20);
      var s24 := PushN(s23, 2, 0x0200);
      var s25 := PushN(s24, 1, 0x84);
      var s26 := PushN(s25, 2, 0x021c);
      var s27 := PushN(s26, 1, 0x00);
      var s28 := PushN(s27, 1, 0x09);
      var s29 := SLoad(s28);
      var s30 := Gas(s29);
      var s31 := Call(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s114(s31, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 80
    * Starting at 0x69b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x06a9);
      assert s1.stack[0] == 0x6a9;
      var s2 := JumpI(s1);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s1.stack[1] > 0 then
        ExecuteFromCFGNode_s116(s2, gas - 1)
      else
        ExecuteFromCFGNode_s115(s2, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 81
    * Starting at 0x69f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 116
    * Segment Id for this node is: 82
    * Starting at 0x6a9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s117(s7, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 83
    * Starting at 0x6b3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0200);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MStore(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s81(s4, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 263
    * Starting at 0x1342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 119
    * Segment Id for this node is: 69
    * Starting at 0x5ac
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s73(s2, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 59
    * Starting at 0x4c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xe2ad025a);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x08ef);
      assert s5.stack[0] == 0x8ef;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s6, gas - 1)
      else
        ExecuteFromCFGNode_s121(s6, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 60
    * Starting at 0x4d0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x84);
      var s2 := CallDataLoad(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 1, 0xa0);
      var s5 := Shr(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s7, gas - 1)
      else
        ExecuteFromCFGNode_s122(s7, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 61
    * Starting at 0x4db
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MStore(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s66(s2, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 114
    * Starting at 0x8ef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xe3bff5ce);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x0903);
      assert s5.stack[0] == 0x903;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s158(s6, gas - 1)
      else
        ExecuteFromCFGNode_s124(s6, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 115
    * Starting at 0x8fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x091d);
      assert s4.stack[0] == 0x91d;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s5, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 119
    * Starting at 0x91d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x23b872dd);
      var s3 := PushN(s2, 2, 0x0100);
      var s4 := MStore(s3);
      var s5 := Caller(s4);
      var s6 := PushN(s5, 2, 0x0120);
      var s7 := MStore(s6);
      var s8 := Address(s7);
      var s9 := PushN(s8, 2, 0x0140);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x04);
      var s12 := CallDataLoad(s11);
      var s13 := PushN(s12, 2, 0x0160);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 1, 0x20);
      var s16 := PushN(s15, 2, 0x0100);
      var s17 := PushN(s16, 1, 0x64);
      var s18 := PushN(s17, 2, 0x011c);
      var s19 := PushN(s18, 1, 0x00);
      var s20 := PushN(s19, 1, 0x0a);
      var s21 := SLoad(s20);
      var s22 := Gas(s21);
      var s23 := Call(s22);
      var s24 := PushN(s23, 2, 0x0957);
      assert s24.stack[0] == 0x957;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s25, gas - 1)
      else
        ExecuteFromCFGNode_s126(s25, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 120
    * Starting at 0x94d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 127
    * Segment Id for this node is: 121
    * Starting at 0x957
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x957 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s128(s7, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 122
    * Starting at 0x961
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x961 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x84);
      var s7 := CallDataLoad(s6);
      var s8 := PushN(s7, 2, 0x0120);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0xa4);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 2, 0x0140);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 4, 0xecb586a5);
      var s15 := PushN(s14, 2, 0x0160);
      var s16 := MStore(s15);
      var s17 := PushN(s16, 1, 0x04);
      var s18 := CallDataLoad(s17);
      var s19 := PushN(s18, 2, 0x0180);
      var s20 := MStore(s19);
      var s21 := PushN(s20, 2, 0x0100);
      var s22 := MLoad(s21);
      var s23 := PushN(s22, 2, 0x01a0);
      var s24 := MStore(s23);
      var s25 := PushN(s24, 2, 0x0120);
      var s26 := MLoad(s25);
      var s27 := PushN(s26, 2, 0x01c0);
      var s28 := MStore(s27);
      var s29 := PushN(s28, 2, 0x0140);
      var s30 := MLoad(s29);
      var s31 := PushN(s30, 2, 0x01e0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s129(s31, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 123
    * Starting at 0x9a0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      var s2 := PushN(s1, 1, 0x08);
      var s3 := SLoad(s2);
      var s4 := ExtCodeSize(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s130(s7, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 124
    * Starting at 0x9aa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x84);
      var s4 := PushN(s3, 2, 0x017c);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 1, 0x08);
      var s7 := SLoad(s6);
      var s8 := Gas(s7);
      var s9 := Call(s8);
      var s10 := PushN(s9, 2, 0x09c8);
      assert s10.stack[0] == 0x9c8;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s11, gas - 1)
      else
        ExecuteFromCFGNode_s131(s11, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 125
    * Starting at 0x9be
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 132
    * Segment Id for this node is: 126
    * Starting at 0x9c8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x70a08231);
      var s3 := PushN(s2, 2, 0x0180);
      var s4 := MStore(s3);
      var s5 := Address(s4);
      var s6 := PushN(s5, 2, 0x01a0);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := PushN(s8, 2, 0x0180);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := PushN(s10, 2, 0x019c);
      var s12 := PushN(s11, 1, 0x00);
      var s13 := SLoad(s12);
      var s14 := Gas(s13);
      var s15 := StaticCall(s14);
      var s16 := PushN(s15, 2, 0x09f4);
      assert s16.stack[0] == 0x9f4;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s134(s17, gas - 1)
      else
        ExecuteFromCFGNode_s133(s17, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 127
    * Starting at 0x9ea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 134
    * Segment Id for this node is: 128
    * Starting at 0x9f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s135(s7, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 129
    * Starting at 0x9fe
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0180);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x24);
      var s6 := CallDataLoad(s5);
      var s7 := PushN(s6, 2, 0x0180);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x44);
      var s10 := CallDataLoad(s9);
      var s11 := PushN(s10, 2, 0x01a0);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 1, 0x64);
      var s14 := CallDataLoad(s13);
      var s15 := PushN(s14, 2, 0x01c0);
      var s16 := MStore(s15);
      var s17 := PushN(s16, 4, 0xecb586a5);
      var s18 := PushN(s17, 2, 0x01e0);
      var s19 := MStore(s18);
      var s20 := PushN(s19, 2, 0x0160);
      var s21 := MLoad(s20);
      var s22 := PushN(s21, 2, 0x0200);
      var s23 := MStore(s22);
      var s24 := PushN(s23, 2, 0x0180);
      var s25 := MLoad(s24);
      var s26 := PushN(s25, 2, 0x0220);
      var s27 := MStore(s26);
      var s28 := PushN(s27, 2, 0x01a0);
      var s29 := MLoad(s28);
      var s30 := PushN(s29, 2, 0x0240);
      var s31 := MStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s136(s31, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 130
    * Starting at 0xa3c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01c0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0260);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x60);
      var s6 := PushN(s5, 2, 0x01e0);
      var s7 := PushN(s6, 1, 0x84);
      var s8 := PushN(s7, 2, 0x01fc);
      var s9 := PushN(s8, 1, 0x00);
      var s10 := PushN(s9, 1, 0x09);
      var s11 := SLoad(s10);
      var s12 := Gas(s11);
      var s13 := Call(s12);
      var s14 := PushN(s13, 2, 0x0a63);
      assert s14.stack[0] == 0xa63;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s138(s15, gas - 1)
      else
        ExecuteFromCFGNode_s137(s15, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 131
    * Starting at 0xa59
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 138
    * Segment Id for this node is: 132
    * Starting at 0xa63
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x5f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s139(s7, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 133
    * Starting at 0xa6d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01e0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x01e0);
      var s4 := PushN(s3, 1, 0x00);
      var s5 := PushN(s4, 1, 0x05);
      var s6 := Dup(s5, 2);
      var s7 := Dup(s6, 4);
      var s8 := MStore(s7);
      var s9 := Add(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s140(s9, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 134
    * Starting at 0xa7c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x70a08231);
      var s3 := PushN(s2, 2, 0x0200);
      var s4 := MStore(s3);
      var s5 := Address(s4);
      var s6 := PushN(s5, 2, 0x0220);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := PushN(s8, 2, 0x0200);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := PushN(s10, 2, 0x021c);
      var s12 := PushN(s11, 1, 0x01);
      var s13 := PushN(s12, 2, 0x01e0);
      var s14 := MLoad(s13);
      var s15 := PushN(s14, 1, 0x05);
      var s16 := Dup(s15, 2);
      var s17 := Lt(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x1342);
      assert s19.stack[0] == 0x1342;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s157(s20, gas - 1)
      else
        ExecuteFromCFGNode_s141(s20, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 135
    * Starting at 0xaa4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x03);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := StaticCall(s5);
      var s7 := PushN(s6, 2, 0x0ab9);
      assert s7.stack[0] == 0xab9;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s8, gas - 1)
      else
        ExecuteFromCFGNode_s142(s8, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 136
    * Starting at 0xaaf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 143
    * Segment Id for this node is: 137
    * Starting at 0xab9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s7, gas - 1)
      else
        ExecuteFromCFGNode_s144(s7, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 138
    * Starting at 0xac3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0200);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := PushN(s6, 2, 0x0240);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 32, 0xa9059cbb00000000000000000000000000000000000000000000000000000000);
      var s10 := PushN(s9, 2, 0x0260);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x0240);
      var s13 := PushN(s12, 1, 0x04);
      var s14 := Dup(s13, 1);
      var s15 := PushN(s14, 1, 0x20);
      var s16 := Dup(s15, 5);
      var s17 := PushN(s16, 2, 0x0280);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Dup(s19, 3);
      var s21 := PushN(s20, 1, 0x20);
      var s22 := Dup(s21, 6);
      var s23 := Add(s22);
      var s24 := PushN(s23, 1, 0x04);
      var s25 := Gas(s24);
      var s26 := StaticCall(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Dup(s28, 1);
      var s30 := MLoad(s29);
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s145(s31, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 139
    * Starting at 0xb14
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      var s2 := Swap(s1, 2);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0xe0);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Dup(s7, 3);
      var s9 := PushN(s8, 2, 0x0280);
      var s10 := Add(s9);
      var s11 := Add(s10);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 1, 0x20);
      var s14 := Dup(s13, 2);
      var s15 := Add(s14);
      var s16 := Swap(s15, 1);
      var s17 := Pop(s16);
      var s18 := PushN(s17, 2, 0x0160);
      var s19 := MLoad(s18);
      var s20 := PushN(s19, 1, 0x20);
      var s21 := Dup(s20, 3);
      var s22 := PushN(s21, 2, 0x0280);
      var s23 := Add(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := PushN(s25, 1, 0x20);
      var s27 := Dup(s26, 2);
      var s28 := Add(s27);
      var s29 := Swap(s28, 1);
      var s30 := Pop(s29);
      var s31 := Dup(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s146(s31, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 140
    * Starting at 0xb3e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0280);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 2, 0x0280);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := PushN(s5, 1, 0x20);
      var s7 := PushN(s6, 2, 0x0320);
      var s8 := PushN(s7, 2, 0x0280);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x02a0);
      var s11 := PushN(s10, 1, 0x00);
      var s12 := PushN(s11, 1, 0x01);
      var s13 := PushN(s12, 2, 0x01e0);
      var s14 := MLoad(s13);
      var s15 := PushN(s14, 1, 0x05);
      var s16 := Dup(s15, 2);
      var s17 := Lt(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x1342);
      assert s19.stack[0] == 0x1342;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s20, gas - 1)
      else
        ExecuteFromCFGNode_s147(s20, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 141
    * Starting at 0xb64
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb64 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x03);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := PushN(s6, 2, 0x0b79);
      assert s7.stack[0] == 0xb79;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s8, gas - 1)
      else
        ExecuteFromCFGNode_s148(s8, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 142
    * Starting at 0xb6f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 149
    * Segment Id for this node is: 143
    * Starting at 0xb79
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0300);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Gt(s6);
      var s8 := PushN(s7, 2, 0x0b8c);
      assert s8.stack[0] == 0xb8c;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s155(s9, gas - 1)
      else
        ExecuteFromCFGNode_s150(s9, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 144
    * Starting at 0xb87
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x0b8e);
      assert s2.stack[0] == 0xb8e;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s3, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 146
    * Starting at 0xb8e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Add(s10);
      var s12 := Dup(s11, 1);
      var s13 := PushN(s12, 2, 0x0200);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := PushN(s15, 1, 0x04);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0200);
      var s25 := MLoad(s24);
      var s26 := Eq(s25);
      var s27 := PushN(s26, 2, 0x0bcd);
      assert s27.stack[0] == 0xbcd;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s153(s28, gas - 1)
      else
        ExecuteFromCFGNode_s152(s28, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 147
    * Starting at 0xbb3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0220);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0200);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Sub(s7);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := Mul(s9);
      var s11 := Shr(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x1342);
      assert s17.stack[0] == 0x1342;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s18, gas - 1)
      else
        ExecuteFromCFGNode_s153(s18, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 148
    * Starting at 0xbcd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbcd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x01);
      var s5 := Add(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 4);
      var s8 := MStore(s7);
      var s9 := Dup(s8, 2);
      var s10 := Eq(s9);
      var s11 := IsZero(s10);
      var s12 := PushN(s11, 2, 0x0a7c);
      assert s12.stack[0] == 0xa7c;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s140(s13, gas - 1)
      else
        ExecuteFromCFGNode_s154(s13, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 149
    * Starting at 0xbdd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Stop(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 155
    * Segment Id for this node is: 145
    * Starting at 0xb8c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s151(s2, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 263
    * Starting at 0x1342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 157
    * Segment Id for this node is: 263
    * Starting at 0x1342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 158
    * Segment Id for this node is: 116
    * Starting at 0x903
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x903 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x4f626a31);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x0be0);
      assert s5.stack[0] == 0xbe0;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s161(s6, gas - 1)
      else
        ExecuteFromCFGNode_s159(s6, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 117
    * Starting at 0x90f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xc4);
      var s2 := CallDataLoad(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 1, 0xa0);
      var s5 := Shr(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s7, gas - 1)
      else
        ExecuteFromCFGNode_s160(s7, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 118
    * Starting at 0x91a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MStore(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s125(s2, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 150
    * Starting at 0xbe0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xf1dc3cc9);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x0bf4);
      assert s5.stack[0] == 0xbf4;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s6, gas - 1)
      else
        ExecuteFromCFGNode_s162(s6, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 151
    * Starting at 0xbec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x0c0e);
      assert s4.stack[0] == 0xc0e;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s5, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 155
    * Starting at 0xc0e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x23b872dd);
      var s3 := PushN(s2, 2, 0x0100);
      var s4 := MStore(s3);
      var s5 := Caller(s4);
      var s6 := PushN(s5, 2, 0x0120);
      var s7 := MStore(s6);
      var s8 := Address(s7);
      var s9 := PushN(s8, 2, 0x0140);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x04);
      var s12 := CallDataLoad(s11);
      var s13 := PushN(s12, 2, 0x0160);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 1, 0x20);
      var s16 := PushN(s15, 2, 0x0100);
      var s17 := PushN(s16, 1, 0x64);
      var s18 := PushN(s17, 2, 0x011c);
      var s19 := PushN(s18, 1, 0x00);
      var s20 := PushN(s19, 1, 0x0a);
      var s21 := SLoad(s20);
      var s22 := Gas(s21);
      var s23 := Call(s22);
      var s24 := PushN(s23, 2, 0x0c48);
      assert s24.stack[0] == 0xc48;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s25, gas - 1)
      else
        ExecuteFromCFGNode_s164(s25, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 156
    * Starting at 0xc3e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 165
    * Segment Id for this node is: 157
    * Starting at 0xc48
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s166(s7, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 158
    * Starting at 0xc52
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x03);
      var s7 := PushN(s6, 1, 0x24);
      var s8 := CallDataLoad(s7);
      var s9 := Lt(s8);
      var s10 := PushN(s9, 2, 0x0c7d);
      assert s10.stack[0] == 0xc7d;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s11, gas - 1)
      else
        ExecuteFromCFGNode_s167(s11, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 159
    * Starting at 0xc66
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc66 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x24);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0x02);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := Lt(s5);
      var s7 := PushN(s6, 2, 0x1342);
      assert s7.stack[0] == 0x1342;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s8, gas - 1)
      else
        ExecuteFromCFGNode_s168(s8, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 160
    * Starting at 0xc72
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Sub(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0100);
      var s9 := MStore(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s169(s9, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 161
    * Starting at 0xc7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xf1dc3cc9);
      var s3 := PushN(s2, 2, 0x0120);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x04);
      var s6 := CallDataLoad(s5);
      var s7 := PushN(s6, 2, 0x0140);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0100);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x0160);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 1, 0x00);
      var s14 := PushN(s13, 2, 0x0180);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 1, 0x08);
      var s17 := SLoad(s16);
      var s18 := ExtCodeSize(s17);
      var s19 := IsZero(s18);
      var s20 := PushN(s19, 2, 0x1342);
      assert s20.stack[0] == 0x1342;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s21, gas - 1)
      else
        ExecuteFromCFGNode_s170(s21, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 162
    * Starting at 0xca5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x64);
      var s4 := PushN(s3, 2, 0x013c);
      assert s4.stack[0] == 0x13c;
      var s5 := PushN(s4, 1, 0x00);
      assert s5.stack[1] == 0x13c;
      var s6 := PushN(s5, 1, 0x08);
      assert s6.stack[2] == 0x13c;
      var s7 := SLoad(s6);
      assert s7.stack[2] == 0x13c;
      var s8 := Gas(s7);
      assert s8.stack[3] == 0x13c;
      var s9 := Call(s8);
      var s10 := PushN(s9, 2, 0x0cc3);
      assert s10.stack[0] == 0xcc3;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s11, gas - 1)
      else
        ExecuteFromCFGNode_s171(s11, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 163
    * Starting at 0xcb9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 172
    * Segment Id for this node is: 164
    * Starting at 0xcc3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x70a08231);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MStore(s3);
      var s5 := Address(s4);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := PushN(s8, 2, 0x0140);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := PushN(s10, 2, 0x015c);
      var s12 := PushN(s11, 1, 0x01);
      var s13 := PushN(s12, 2, 0x0100);
      var s14 := MLoad(s13);
      var s15 := PushN(s14, 1, 0x03);
      var s16 := Dup(s15, 2);
      var s17 := Lt(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x1342);
      assert s19.stack[0] == 0x1342;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s20, gas - 1)
      else
        ExecuteFromCFGNode_s173(s20, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 165
    * Starting at 0xceb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xceb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := SLoad(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := PushN(s4, 2, 0x0cfd);
      assert s5.stack[0] == 0xcfd;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s6, gas - 1)
      else
        ExecuteFromCFGNode_s174(s6, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 166
    * Starting at 0xcf3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 175
    * Segment Id for this node is: 167
    * Starting at 0xcfd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s176(s7, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 168
    * Starting at 0xd07
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd07 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0140);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0120);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x0100);
      var s6 := MLoad(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x0d28);
      assert s8.stack[0] == 0xd28;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s190(s9, gas - 1)
      else
        ExecuteFromCFGNode_s177(s9, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 169
    * Starting at 0xd18
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x44);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 2, 0x0120);
      var s4 := MLoad(s3);
      var s5 := Lt(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s178(s7, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 170
    * Starting at 0xd24
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0d81);
      assert s1.stack[0] == 0xd81;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s2, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 176
    * Starting at 0xd81
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := PushN(s3, 2, 0x0180);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 32, 0xa9059cbb00000000000000000000000000000000000000000000000000000000);
      var s7 := PushN(s6, 2, 0x01a0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0180);
      var s10 := PushN(s9, 1, 0x04);
      var s11 := Dup(s10, 1);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Dup(s12, 5);
      var s14 := PushN(s13, 2, 0x01c0);
      var s15 := Add(s14);
      var s16 := Add(s15);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 6);
      var s20 := Add(s19);
      var s21 := PushN(s20, 1, 0x04);
      var s22 := Gas(s21);
      var s23 := StaticCall(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Dup(s25, 1);
      var s27 := MLoad(s26);
      var s28 := Dup(s27, 3);
      var s29 := Add(s28);
      var s30 := Swap(s29, 2);
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s180(s31, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 177
    * Starting at 0xdce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x20);
      var s5 := Dup(s4, 3);
      var s6 := PushN(s5, 2, 0x01c0);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Dup(s10, 2);
      var s12 := Add(s11);
      var s13 := Swap(s12, 1);
      var s14 := Pop(s13);
      var s15 := PushN(s14, 2, 0x0120);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 1, 0x20);
      var s18 := Dup(s17, 3);
      var s19 := PushN(s18, 2, 0x01c0);
      var s20 := Add(s19);
      var s21 := Add(s20);
      var s22 := MStore(s21);
      var s23 := PushN(s22, 1, 0x20);
      var s24 := Dup(s23, 2);
      var s25 := Add(s24);
      var s26 := Swap(s25, 1);
      var s27 := Pop(s26);
      var s28 := Dup(s27, 1);
      var s29 := PushN(s28, 2, 0x01c0);
      var s30 := MStore(s29);
      var s31 := PushN(s30, 2, 0x01c0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s181(s31, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 178
    * Starting at 0xdfc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x0260);
      var s5 := PushN(s4, 2, 0x01c0);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x01e0);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 1, 0x01);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 1, 0x05);
      var s13 := Dup(s12, 2);
      var s14 := Lt(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x1342);
      assert s16.stack[0] == 0x1342;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s17, gas - 1)
      else
        ExecuteFromCFGNode_s182(s17, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 179
    * Starting at 0xe1a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x03);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := PushN(s6, 2, 0x0e2f);
      assert s7.stack[0] == 0xe2f;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s184(s8, gas - 1)
      else
        ExecuteFromCFGNode_s183(s8, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 180
    * Starting at 0xe25
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 184
    * Segment Id for this node is: 181
    * Starting at 0xe2f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0240);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Gt(s6);
      var s8 := PushN(s7, 2, 0x0e42);
      assert s8.stack[0] == 0xe42;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s9, gas - 1)
      else
        ExecuteFromCFGNode_s185(s9, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 182
    * Starting at 0xe3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x0e44);
      assert s2.stack[0] == 0xe44;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s3, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 184
    * Starting at 0xe44
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Add(s10);
      var s12 := Dup(s11, 1);
      var s13 := PushN(s12, 2, 0x0140);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := PushN(s15, 1, 0x04);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0140);
      var s25 := MLoad(s24);
      var s26 := Eq(s25);
      var s27 := PushN(s26, 2, 0x0e83);
      assert s27.stack[0] == 0xe83;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s28, gas - 1)
      else
        ExecuteFromCFGNode_s187(s28, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 185
    * Starting at 0xe69
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0160);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Sub(s7);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := Mul(s9);
      var s11 := Shr(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x1342);
      assert s17.stack[0] == 0x1342;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s18, gas - 1)
      else
        ExecuteFromCFGNode_s188(s18, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 186
    * Starting at 0xe83
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe83 as nat
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

  /** Node 189
    * Segment Id for this node is: 183
    * Starting at 0xe42
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s186(s2, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 171
    * Starting at 0xd28
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x1a4d01d2);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x0120);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0160);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x24);
      var s10 := CallDataLoad(s9);
      var s11 := Dup(s10, 1);
      var s12 := PushN(s11, 1, 0x7f);
      var s13 := Shr(s12);
      var s14 := PushN(s13, 2, 0x1342);
      assert s14.stack[0] == 0x1342;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s15, gas - 1)
      else
        ExecuteFromCFGNode_s191(s15, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 172
    * Starting at 0xd45
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd45 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0180);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x44);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 2, 0x01a0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 2, 0x0140);
      var s9 := PushN(s8, 1, 0x64);
      var s10 := PushN(s9, 2, 0x015c);
      var s11 := PushN(s10, 1, 0x00);
      var s12 := PushN(s11, 1, 0x09);
      var s13 := SLoad(s12);
      var s14 := Gas(s13);
      var s15 := Call(s14);
      var s16 := PushN(s15, 2, 0x0d6f);
      assert s16.stack[0] == 0xd6f;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s17, gas - 1)
      else
        ExecuteFromCFGNode_s192(s17, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 173
    * Starting at 0xd65
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 193
    * Segment Id for this node is: 174
    * Starting at 0xd6f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s194(s7, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 175
    * Starting at 0xd79
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0140);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0120);
      var s4 := MStore(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s179(s4, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 152
    * Starting at 0xbf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x0fbcee6e);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x0e85);
      assert s5.stack[0] == 0xe85;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s6, gas - 1)
      else
        ExecuteFromCFGNode_s196(s6, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 153
    * Starting at 0xc00
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x64);
      var s2 := CallDataLoad(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 1, 0xa0);
      var s5 := Shr(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s7, gas - 1)
      else
        ExecuteFromCFGNode_s197(s7, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 154
    * Starting at 0xc0b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MStore(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s163(s2, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 187
    * Starting at 0xe85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x85f11d1e);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x10a6);
      assert s5.stack[0] == 0x10a6;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s232(s6, gas - 1)
      else
        ExecuteFromCFGNode_s199(s6, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 188
    * Starting at 0xe91
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x03);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 1, 0x24);
      var s5 := CallDataLoad(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Lt(s7);
      var s9 := PushN(s8, 2, 0x0ea5);
      assert s9.stack[0] == 0xea5;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s10, gas - 1)
      else
        ExecuteFromCFGNode_s200(s10, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 189
    * Starting at 0xea0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x0ea7);
      assert s2.stack[0] == 0xea7;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s3, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 191
    * Starting at 0xea7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x0f14);
      assert s8.stack[0] == 0xf14;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s209(s9, gas - 1)
      else
        ExecuteFromCFGNode_s202(s9, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 192
    * Starting at 0xeb2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 4, 0x5e0d443f);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 1, 0x04);
      var s5 := CallDataLoad(s4);
      var s6 := Dup(s5, 1);
      var s7 := PushN(s6, 1, 0x7f);
      var s8 := Shr(s7);
      var s9 := PushN(s8, 2, 0x1342);
      assert s9.stack[0] == 0x1342;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s10, gas - 1)
      else
        ExecuteFromCFGNode_s203(s10, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 193
    * Starting at 0xec5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x24);
      var s4 := CallDataLoad(s3);
      var s5 := Dup(s4, 1);
      var s6 := PushN(s5, 1, 0x7f);
      var s7 := Shr(s6);
      var s8 := PushN(s7, 2, 0x1342);
      assert s8.stack[0] == 0x1342;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s9, gas - 1)
      else
        ExecuteFromCFGNode_s204(s9, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 194
    * Starting at 0xed4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0120);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x44);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 2, 0x0140);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 1, 0xe0);
      var s9 := PushN(s8, 1, 0x64);
      var s10 := PushN(s9, 1, 0xfc);
      var s11 := PushN(s10, 1, 0x09);
      var s12 := SLoad(s11);
      var s13 := Gas(s12);
      var s14 := StaticCall(s13);
      var s15 := PushN(s14, 2, 0x0efa);
      assert s15.stack[0] == 0xefa;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s16, gas - 1)
      else
        ExecuteFromCFGNode_s205(s16, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 195
    * Starting at 0xef0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 206
    * Segment Id for this node is: 196
    * Starting at 0xefa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s207(s7, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 197
    * Starting at 0xf04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := PushN(s6, 2, 0x10a4);
      assert s7.stack[0] == 0x10a4;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s8, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 221
    * Starting at 0x10a4
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Return(s1);
      // Segment is terminal (Revert, Stop or Return)
      s2
  }

  /** Node 209
    * Segment Id for this node is: 198
    * Starting at 0xf14
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x44);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 1, 0xe0);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x40);
      var s7 := CallDataSize(s6);
      var s8 := PushN(s7, 2, 0x0100);
      var s9 := CallDataCopy(s8);
      var s10 := PushN(s9, 1, 0x03);
      var s11 := PushN(s10, 1, 0x24);
      var s12 := CallDataLoad(s11);
      var s13 := Lt(s12);
      var s14 := PushN(s13, 2, 0x0f43);
      assert s14.stack[0] == 0xf43;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s15, gas - 1)
      else
        ExecuteFromCFGNode_s210(s15, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 199
    * Starting at 0xf2c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x24);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0x02);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := Lt(s5);
      var s7 := PushN(s6, 2, 0x1342);
      assert s7.stack[0] == 0x1342;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s8, gas - 1)
      else
        ExecuteFromCFGNode_s211(s8, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 200
    * Starting at 0xf38
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf38 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Sub(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0120);
      var s9 := MStore(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s212(s9, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 201
    * Starting at 0xf43
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x03);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := CallDataLoad(s3);
      var s5 := Lt(s4);
      var s6 := PushN(s5, 2, 0x0f69);
      assert s6.stack[0] == 0xf69;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s225(s7, gas - 1)
      else
        ExecuteFromCFGNode_s213(s7, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 202
    * Starting at 0xf4e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0x02);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := Lt(s5);
      var s7 := PushN(s6, 2, 0x1342);
      assert s7.stack[0] == 0x1342;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s8, gas - 1)
      else
        ExecuteFromCFGNode_s214(s8, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 203
    * Starting at 0xf5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Sub(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0100);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x0fdd);
      assert s10.stack[0] == 0xfdd;
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s11, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 210
    * Starting at 0xfdd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x556d6e9f);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x0100);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0180);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0120);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x01a0);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 1, 0xe0);
      var s14 := MLoad(s13);
      var s15 := PushN(s14, 2, 0x01c0);
      var s16 := MStore(s15);
      var s17 := PushN(s16, 1, 0x20);
      var s18 := PushN(s17, 2, 0x0160);
      var s19 := PushN(s18, 1, 0x64);
      var s20 := PushN(s19, 2, 0x017c);
      var s21 := PushN(s20, 1, 0x08);
      var s22 := SLoad(s21);
      var s23 := Gas(s22);
      var s24 := StaticCall(s23);
      var s25 := PushN(s24, 2, 0x101b);
      assert s25.stack[0] == 0x101b;
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s217(s26, gas - 1)
      else
        ExecuteFromCFGNode_s216(s26, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 211
    * Starting at 0x1011
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1011 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 217
    * Segment Id for this node is: 212
    * Starting at 0x101b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s218(s7, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 213
    * Starting at 0x1025
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1025 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0160);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x0120);
      var s6 := MLoad(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x104b);
      assert s8.stack[0] == 0x104b;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s220(s9, gas - 1)
      else
        ExecuteFromCFGNode_s219(s9, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 214
    * Starting at 0x1036
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1036 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0140);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := PushN(s6, 2, 0x10a4);
      assert s7.stack[0] == 0x10a4;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s8, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 216
    * Starting at 0x104b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xcc2b27d7);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x0140);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0180);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x24);
      var s10 := CallDataLoad(s9);
      var s11 := Dup(s10, 1);
      var s12 := PushN(s11, 1, 0x7f);
      var s13 := Shr(s12);
      var s14 := PushN(s13, 2, 0x1342);
      assert s14.stack[0] == 0x1342;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s15, gas - 1)
      else
        ExecuteFromCFGNode_s221(s15, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 217
    * Starting at 0x1068
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1068 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01a0);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x0160);
      var s5 := PushN(s4, 1, 0x44);
      var s6 := PushN(s5, 2, 0x017c);
      var s7 := PushN(s6, 1, 0x09);
      var s8 := SLoad(s7);
      var s9 := Gas(s8);
      var s10 := StaticCall(s9);
      var s11 := PushN(s10, 2, 0x1089);
      assert s11.stack[0] == 0x1089;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s223(s12, gas - 1)
      else
        ExecuteFromCFGNode_s222(s12, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 218
    * Starting at 0x107f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 223
    * Segment Id for this node is: 219
    * Starting at 0x1089
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1089 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s224(s7, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 220
    * Starting at 0x1093
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1093 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0160);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x01c0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x01c0);
      var s7 := PushN(s6, 2, 0x10a4);
      assert s7.stack[0] == 0x10a4;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s8, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 204
    * Starting at 0xf69
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x60);
      var s3 := CallDataSize(s2);
      var s4 := PushN(s3, 2, 0x0140);
      var s5 := CallDataCopy(s4);
      var s6 := PushN(s5, 1, 0xe0);
      var s7 := MLoad(s6);
      var s8 := PushN(s7, 2, 0x0140);
      var s9 := PushN(s8, 1, 0x04);
      var s10 := CallDataLoad(s9);
      var s11 := PushN(s10, 1, 0x03);
      var s12 := Dup(s11, 2);
      var s13 := Lt(s12);
      var s14 := IsZero(s13);
      var s15 := PushN(s14, 2, 0x1342);
      assert s15.stack[0] == 0x1342;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s16, gas - 1)
      else
        ExecuteFromCFGNode_s226(s16, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 205
    * Starting at 0xf83
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := Mul(s1);
      var s3 := Add(s2);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 4, 0x3883e119);
      var s6 := PushN(s5, 2, 0x01a0);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x0140);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x01c0);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x0160);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 2, 0x01e0);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 2, 0x0180);
      var s17 := MLoad(s16);
      var s18 := PushN(s17, 2, 0x0200);
      var s19 := MStore(s18);
      var s20 := PushN(s19, 1, 0x01);
      var s21 := PushN(s20, 2, 0x0220);
      var s22 := MStore(s21);
      var s23 := PushN(s22, 1, 0x20);
      var s24 := PushN(s23, 2, 0x01a0);
      var s25 := PushN(s24, 1, 0x84);
      var s26 := PushN(s25, 2, 0x01bc);
      var s27 := PushN(s26, 1, 0x09);
      var s28 := SLoad(s27);
      var s29 := Gas(s28);
      var s30 := StaticCall(s29);
      var s31 := PushN(s30, 2, 0x0fcc);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s227(s31, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 206
    * Starting at 0xfc1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0xfcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpI(s0);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s0.stack[1] > 0 then
        ExecuteFromCFGNode_s229(s1, gas - 1)
      else
        ExecuteFromCFGNode_s228(s1, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 207
    * Starting at 0xfc2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 229
    * Segment Id for this node is: 208
    * Starting at 0xfcc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s230(s7, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 209
    * Starting at 0xfd6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01a0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := MStore(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s215(s4, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 190
    * Starting at 0xea5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s201(s2, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 222
    * Starting at 0x10a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x7ede89c5);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x119f);
      assert s5.stack[0] == 0x119f;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s243(s6, gas - 1)
      else
        ExecuteFromCFGNode_s233(s6, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 223
    * Starting at 0x10b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xa4);
      var s2 := CallDataLoad(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 1, 0x01);
      var s5 := Shr(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s7, gas - 1)
      else
        ExecuteFromCFGNode_s234(s7, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 224
    * Starting at 0x10bd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 2, 0x0100);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x24);
      var s8 := CallDataLoad(s7);
      var s9 := PushN(s8, 2, 0x0120);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x44);
      var s12 := CallDataLoad(s11);
      var s13 := PushN(s12, 2, 0x0140);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 4, 0x3883e119);
      var s16 := PushN(s15, 2, 0x0180);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 2, 0x0100);
      var s19 := MLoad(s18);
      var s20 := PushN(s19, 2, 0x01a0);
      var s21 := MStore(s20);
      var s22 := PushN(s21, 2, 0x0120);
      var s23 := MLoad(s22);
      var s24 := PushN(s23, 2, 0x01c0);
      var s25 := MStore(s24);
      var s26 := PushN(s25, 2, 0x0140);
      var s27 := MLoad(s26);
      var s28 := PushN(s27, 2, 0x01e0);
      var s29 := MStore(s28);
      var s30 := PushN(s29, 1, 0xe0);
      var s31 := MLoad(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s235(s31, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 225
    * Starting at 0x10f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0200);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x0180);
      var s5 := PushN(s4, 1, 0x84);
      var s6 := PushN(s5, 2, 0x019c);
      var s7 := PushN(s6, 1, 0x09);
      var s8 := SLoad(s7);
      var s9 := Gas(s8);
      var s10 := StaticCall(s9);
      var s11 := PushN(s10, 2, 0x111a);
      assert s11.stack[0] == 0x111a;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s237(s12, gas - 1)
      else
        ExecuteFromCFGNode_s236(s12, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 226
    * Starting at 0x1110
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1110 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 237
    * Segment Id for this node is: 227
    * Starting at 0x111a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s238(s7, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 228
    * Starting at 0x1124
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0180);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x0160);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0180);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x64);
      var s10 := CallDataLoad(s9);
      var s11 := PushN(s10, 2, 0x01a0);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 1, 0x84);
      var s14 := CallDataLoad(s13);
      var s15 := PushN(s14, 2, 0x01c0);
      var s16 := MStore(s15);
      var s17 := PushN(s16, 4, 0x3883e119);
      var s18 := PushN(s17, 2, 0x01e0);
      var s19 := MStore(s18);
      var s20 := PushN(s19, 2, 0x0180);
      var s21 := MLoad(s20);
      var s22 := PushN(s21, 2, 0x0200);
      var s23 := MStore(s22);
      var s24 := PushN(s23, 2, 0x01a0);
      var s25 := MLoad(s24);
      var s26 := PushN(s25, 2, 0x0220);
      var s27 := MStore(s26);
      var s28 := PushN(s27, 2, 0x01c0);
      var s29 := MLoad(s28);
      var s30 := PushN(s29, 2, 0x0240);
      var s31 := MStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s239(s31, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 229
    * Starting at 0x1163
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1163 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0260);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x01e0);
      var s7 := PushN(s6, 1, 0x84);
      var s8 := PushN(s7, 2, 0x01fc);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := SLoad(s9);
      var s11 := Gas(s10);
      var s12 := StaticCall(s11);
      var s13 := PushN(s12, 2, 0x1187);
      assert s13.stack[0] == 0x1187;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s241(s14, gas - 1)
      else
        ExecuteFromCFGNode_s240(s14, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 230
    * Starting at 0x117d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 241
    * Segment Id for this node is: 231
    * Starting at 0x1187
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1187 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s242(s7, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 232
    * Starting at 0x1191
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01e0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0280);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x0280);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 243
    * Segment Id for this node is: 233
    * Starting at 0x119f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x119f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x4fb08c5e);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x12aa);
      assert s5.stack[0] == 0x12aa;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s259(s6, gas - 1)
      else
        ExecuteFromCFGNode_s244(s6, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 234
    * Starting at 0x11ab
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x03);
      var s2 := PushN(s1, 1, 0x24);
      var s3 := CallDataLoad(s2);
      var s4 := Lt(s3);
      var s5 := PushN(s4, 2, 0x1210);
      assert s5.stack[0] == 0x1210;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s251(s6, gas - 1)
      else
        ExecuteFromCFGNode_s245(s6, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 235
    * Starting at 0x11b5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 4, 0x4fb08c5e);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 1, 0x04);
      var s5 := CallDataLoad(s4);
      var s6 := PushN(s5, 2, 0x0100);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x24);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 1, 0x02);
      var s11 := Dup(s10, 1);
      var s12 := Dup(s11, 3);
      var s13 := Lt(s12);
      var s14 := PushN(s13, 2, 0x1342);
      assert s14.stack[0] == 0x1342;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s15, gas - 1)
      else
        ExecuteFromCFGNode_s246(s15, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 236
    * Starting at 0x11d0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Sub(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0120);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := PushN(s10, 1, 0xe0);
      var s12 := PushN(s11, 1, 0x44);
      var s13 := PushN(s12, 1, 0xfc);
      var s14 := PushN(s13, 1, 0x08);
      var s15 := SLoad(s14);
      var s16 := Gas(s15);
      var s17 := StaticCall(s16);
      var s18 := PushN(s17, 2, 0x11f6);
      assert s18.stack[0] == 0x11f6;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s19, gas - 1)
      else
        ExecuteFromCFGNode_s247(s19, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 237
    * Starting at 0x11ec
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 248
    * Segment Id for this node is: 238
    * Starting at 0x11f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s249(s7, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 239
    * Starting at 0x1200
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1200 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x0140);
      var s7 := PushN(s6, 2, 0x12a8);
      assert s7.stack[0] == 0x12a8;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s8, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 248
    * Starting at 0x12a8
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Return(s1);
      // Segment is terminal (Revert, Stop or Return)
      s2
  }

  /** Node 251
    * Segment Id for this node is: 240
    * Starting at 0x1210
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1210 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x4fb08c5e);
      var s3 := PushN(s2, 2, 0x0100);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x04);
      var s6 := CallDataLoad(s5);
      var s7 := PushN(s6, 2, 0x0120);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x00);
      var s10 := PushN(s9, 2, 0x0140);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := PushN(s12, 2, 0x0100);
      var s14 := PushN(s13, 1, 0x44);
      var s15 := PushN(s14, 2, 0x011c);
      var s16 := PushN(s15, 1, 0x08);
      var s17 := SLoad(s16);
      var s18 := Gas(s17);
      var s19 := StaticCall(s18);
      var s20 := PushN(s19, 2, 0x1244);
      assert s20.stack[0] == 0x1244;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s253(s21, gas - 1)
      else
        ExecuteFromCFGNode_s252(s21, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 241
    * Starting at 0x123a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 253
    * Segment Id for this node is: 242
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s254(s7, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 243
    * Starting at 0x124e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 4, 0xcc2b27d7);
      var s6 := PushN(s5, 2, 0x0100);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0xe0);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x0120);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 1, 0x24);
      var s13 := CallDataLoad(s12);
      var s14 := Dup(s13, 1);
      var s15 := PushN(s14, 1, 0x7f);
      var s16 := Shr(s15);
      var s17 := PushN(s16, 2, 0x1342);
      assert s17.stack[0] == 0x1342;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s18, gas - 1)
      else
        ExecuteFromCFGNode_s255(s18, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 244
    * Starting at 0x1270
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1270 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0140);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := PushN(s4, 1, 0x44);
      var s6 := PushN(s5, 2, 0x011c);
      var s7 := PushN(s6, 1, 0x09);
      var s8 := SLoad(s7);
      var s9 := Gas(s8);
      var s10 := StaticCall(s9);
      var s11 := PushN(s10, 2, 0x1291);
      assert s11.stack[0] == 0x1291;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s257(s12, gas - 1)
      else
        ExecuteFromCFGNode_s256(s12, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 245
    * Starting at 0x1287
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1287 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 257
    * Segment Id for this node is: 246
    * Starting at 0x1291
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1291 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1342);
      assert s6.stack[0] == 0x1342;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s7, gas - 1)
      else
        ExecuteFromCFGNode_s258(s7, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 247
    * Starting at 0x129b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x0160);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s250(s6, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 249
    * Starting at 0x12aa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xc6610657);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x12ce);
      assert s5.stack[0] == 0x12ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s262(s6, gas - 1)
      else
        ExecuteFromCFGNode_s260(s6, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 250
    * Starting at 0x12b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x01);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 1, 0x03);
      var s5 := Dup(s4, 2);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x1342);
      assert s8.stack[0] == 0x1342;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s9, gas - 1)
      else
        ExecuteFromCFGNode_s261(s9, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 251
    * Starting at 0x12c4
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := SLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 1, 0xe0);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 262
    * Segment Id for this node is: 252
    * Starting at 0x12ce
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xb9947eb0);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x12f5);
      assert s5.stack[0] == 0x12f5;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s265(s6, gas - 1)
      else
        ExecuteFromCFGNode_s263(s6, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 253
    * Starting at 0x12da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x01);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 1, 0x05);
      var s5 := Dup(s4, 2);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x1342);
      assert s8.stack[0] == 0x1342;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s9, gas - 1)
      else
        ExecuteFromCFGNode_s264(s9, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 254
    * Starting at 0x12e8
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x03);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 1, 0xe0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 1, 0xe0);
      var s9 := Return(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 265
    * Segment Id for this node is: 255
    * Starting at 0x12f5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x16f0115b);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x130c);
      assert s5.stack[0] == 0x130c;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s6, gas - 1)
      else
        ExecuteFromCFGNode_s266(s6, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 256
    * Starting at 0x1301
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1301 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x08);
      var s2 := SLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 1, 0xe0);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 267
    * Segment Id for this node is: 257
    * Starting at 0x130c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x130c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x5d6362bb);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x1323);
      assert s5.stack[0] == 0x1323;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s269(s6, gas - 1)
      else
        ExecuteFromCFGNode_s268(s6, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 258
    * Starting at 0x1318
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1318 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x09);
      var s2 := SLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 1, 0xe0);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 269
    * Segment Id for this node is: 259
    * Starting at 0x1323
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1323 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xfc0c546a);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x133a);
      assert s5.stack[0] == 0x133a;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s271(s6, gas - 1)
      else
        ExecuteFromCFGNode_s270(s6, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 260
    * Starting at 0x132f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x0a);
      var s2 := SLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 1, 0xe0);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 271
    * Segment Id for this node is: 261
    * Starting at 0x133a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x133a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s2(s2, gas - 1)
  }
}
