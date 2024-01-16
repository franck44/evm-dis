
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
      var s1 := PushN(s0, 2, 0x17c8);
      assert s1.stack[0] == 0x17c8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s2(s2, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 284
    * Starting at 0x17c8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c8 as nat
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
      var s2 := PushN(s1, 1, 0x00);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 1, 0x1c);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 16, 0x7fffffffffffffffffffffffffffffff);
      var s7 := PushN(s6, 1, 0x40);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x00);
      var s10 := MLoad(s9);
      var s11 := CallValue(s10);
      var s12 := PushN(s11, 2, 0x17ce);
      assert s12.stack[0] == 0x17ce;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s13, gas - 1)
      else
        ExecuteFromCFGNode_s4(s13, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 3
    * Starting at 0x30
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 4, 0x84738499);
      var s2 := Dup(s1, 2);
      var s3 := Eq(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x0045);
      assert s5.stack[0] == 0x45;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s6, gas - 1)
      else
        ExecuteFromCFGNode_s5(s6, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 4
    * Starting at 0x3c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 2, 0x0140);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x0070);
      assert s4.stack[0] == 0x70;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 9
    * Starting at 0x70
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := CallDataSize(s2);
      var s4 := PushN(s3, 2, 0x0160);
      var s5 := CallDataCopy(s4);
      var s6 := PushN(s5, 2, 0x0240);
      assert s6.stack[0] == 0x240;
      var s7 := PushN(s6, 1, 0x00);
      assert s7.stack[1] == 0x240;
      var s8 := PushN(s7, 1, 0x03);
      assert s8.stack[2] == 0x240;
      var s9 := Dup(s8, 2);
      assert s9.stack[3] == 0x240;
      var s10 := Dup(s9, 4);
      assert s10.stack[0] == 0x240;
      assert s10.stack[4] == 0x240;
      var s11 := MStore(s10);
      assert s11.stack[2] == 0x240;
      var s12 := Add(s11);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s7(s12, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 10
    * Starting at 0x83
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x240;
      var s2 := PushN(s1, 1, 0x04);
      assert s2.stack[2] == 0x240;
      var s3 := PushN(s2, 2, 0x0240);
      assert s3.stack[0] == 0x240;
      assert s3.stack[3] == 0x240;
      var s4 := MLoad(s3);
      assert s4.stack[3] == 0x240;
      var s5 := PushN(s4, 1, 0x05);
      assert s5.stack[4] == 0x240;
      var s6 := Dup(s5, 2);
      assert s6.stack[5] == 0x240;
      var s7 := Lt(s6);
      assert s7.stack[4] == 0x240;
      var s8 := IsZero(s7);
      assert s8.stack[4] == 0x240;
      var s9 := PushN(s8, 2, 0x17ce);
      assert s9.stack[0] == 0x17ce;
      assert s9.stack[5] == 0x240;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s10, gas - 1)
      else
        ExecuteFromCFGNode_s8(s10, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 11
    * Starting at 0x93
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[4] == 0x240;
      var s2 := Mul(s1);
      assert s2.stack[3] == 0x240;
      var s3 := Add(s2);
      assert s3.stack[2] == 0x240;
      var s4 := CallDataLoad(s3);
      assert s4.stack[2] == 0x240;
      var s5 := PushN(s4, 2, 0x0260);
      assert s5.stack[3] == 0x240;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0x240;
      var s7 := PushN(s6, 1, 0x00);
      assert s7.stack[2] == 0x240;
      var s8 := PushN(s7, 2, 0x0260);
      assert s8.stack[3] == 0x240;
      var s9 := MLoad(s8);
      assert s9.stack[3] == 0x240;
      var s10 := Xor(s9);
      assert s10.stack[2] == 0x240;
      var s11 := IsZero(s10);
      assert s11.stack[2] == 0x240;
      var s12 := PushN(s11, 2, 0x0240);
      assert s12.stack[0] == 0x240;
      assert s12.stack[3] == 0x240;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s26(s13, gas - 1)
      else
        ExecuteFromCFGNode_s9(s13, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 12
    * Starting at 0xa8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x01);
      assert s1.stack[2] == 0x240;
      var s2 := PushN(s1, 2, 0x0240);
      assert s2.stack[0] == 0x240;
      assert s2.stack[3] == 0x240;
      var s3 := MLoad(s2);
      assert s3.stack[3] == 0x240;
      var s4 := PushN(s3, 1, 0x05);
      assert s4.stack[4] == 0x240;
      var s5 := Dup(s4, 2);
      assert s5.stack[5] == 0x240;
      var s6 := Lt(s5);
      assert s6.stack[4] == 0x240;
      var s7 := IsZero(s6);
      assert s7.stack[4] == 0x240;
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      assert s8.stack[5] == 0x240;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s9, gas - 1)
      else
        ExecuteFromCFGNode_s10(s9, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 13
    * Starting at 0xb7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      assert s1.stack[2] == 0x240;
      var s2 := PushN(s1, 1, 0x04);
      assert s2.stack[3] == 0x240;
      var s3 := Add(s2);
      assert s3.stack[2] == 0x240;
      var s4 := SLoad(s3);
      assert s4.stack[2] == 0x240;
      var s5 := PushN(s4, 2, 0x0280);
      assert s5.stack[3] == 0x240;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0x240;
      var s7 := PushN(s6, 1, 0x00);
      assert s7.stack[2] == 0x240;
      var s8 := PushN(s7, 1, 0x04);
      assert s8.stack[3] == 0x240;
      var s9 := PushN(s8, 2, 0x0300);
      assert s9.stack[4] == 0x240;
      var s10 := MStore(s9);
      assert s10.stack[2] == 0x240;
      var s11 := PushN(s10, 32, 0x23b872dd00000000000000000000000000000000000000000000000000000000);
      assert s11.stack[3] == 0x240;
      var s12 := PushN(s11, 2, 0x0320);
      assert s12.stack[4] == 0x240;
      var s13 := MStore(s12);
      assert s13.stack[2] == 0x240;
      var s14 := PushN(s13, 2, 0x0300);
      assert s14.stack[3] == 0x240;
      var s15 := PushN(s14, 1, 0x04);
      assert s15.stack[4] == 0x240;
      var s16 := Dup(s15, 1);
      assert s16.stack[5] == 0x240;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[6] == 0x240;
      var s18 := Dup(s17, 5);
      assert s18.stack[7] == 0x240;
      var s19 := PushN(s18, 2, 0x0360);
      assert s19.stack[8] == 0x240;
      var s20 := Add(s19);
      assert s20.stack[7] == 0x240;
      var s21 := Add(s20);
      assert s21.stack[6] == 0x240;
      var s22 := Dup(s21, 3);
      assert s22.stack[7] == 0x240;
      var s23 := PushN(s22, 1, 0x20);
      assert s23.stack[8] == 0x240;
      var s24 := Dup(s23, 6);
      assert s24.stack[9] == 0x240;
      var s25 := Add(s24);
      assert s25.stack[8] == 0x240;
      var s26 := PushN(s25, 1, 0x00);
      assert s26.stack[9] == 0x240;
      var s27 := PushN(s26, 1, 0x04);
      assert s27.stack[10] == 0x240;
      var s28 := Gas(s27);
      assert s28.stack[11] == 0x240;
      var s29 := Call(s28);
      assert s29.stack[5] == 0x240;
      var s30 := Pop(s29);
      assert s30.stack[4] == 0x240;
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s11(s31, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 14
    * Starting at 0x108
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[4] == 0x240;
      var s2 := MLoad(s1);
      assert s2.stack[4] == 0x240;
      var s3 := Dup(s2, 3);
      assert s3.stack[5] == 0x240;
      var s4 := Add(s3);
      assert s4.stack[4] == 0x240;
      var s5 := Swap(s4, 2);
      assert s5.stack[4] == 0x240;
      var s6 := Pop(s5);
      assert s6.stack[3] == 0x240;
      var s7 := Pop(s6);
      assert s7.stack[2] == 0x240;
      var s8 := Caller(s7);
      assert s8.stack[3] == 0x240;
      var s9 := PushN(s8, 1, 0x20);
      assert s9.stack[4] == 0x240;
      var s10 := Dup(s9, 3);
      assert s10.stack[5] == 0x240;
      var s11 := PushN(s10, 2, 0x0360);
      assert s11.stack[6] == 0x240;
      var s12 := Add(s11);
      assert s12.stack[5] == 0x240;
      var s13 := Add(s12);
      assert s13.stack[4] == 0x240;
      var s14 := MStore(s13);
      assert s14.stack[2] == 0x240;
      var s15 := PushN(s14, 1, 0x20);
      assert s15.stack[3] == 0x240;
      var s16 := Dup(s15, 2);
      assert s16.stack[4] == 0x240;
      var s17 := Add(s16);
      assert s17.stack[3] == 0x240;
      var s18 := Swap(s17, 1);
      assert s18.stack[3] == 0x240;
      var s19 := Pop(s18);
      assert s19.stack[2] == 0x240;
      var s20 := Address(s19);
      assert s20.stack[3] == 0x240;
      var s21 := PushN(s20, 1, 0x20);
      assert s21.stack[4] == 0x240;
      var s22 := Dup(s21, 3);
      assert s22.stack[5] == 0x240;
      var s23 := PushN(s22, 2, 0x0360);
      assert s23.stack[6] == 0x240;
      var s24 := Add(s23);
      assert s24.stack[5] == 0x240;
      var s25 := Add(s24);
      assert s25.stack[4] == 0x240;
      var s26 := MStore(s25);
      assert s26.stack[2] == 0x240;
      var s27 := PushN(s26, 1, 0x20);
      assert s27.stack[3] == 0x240;
      var s28 := Dup(s27, 2);
      assert s28.stack[4] == 0x240;
      var s29 := Add(s28);
      assert s29.stack[3] == 0x240;
      var s30 := Swap(s29, 1);
      assert s30.stack[3] == 0x240;
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s12(s31, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 15
    * Starting at 0x12f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0260);
      assert s1.stack[3] == 0x240;
      var s2 := MLoad(s1);
      assert s2.stack[3] == 0x240;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[4] == 0x240;
      var s4 := Dup(s3, 3);
      assert s4.stack[5] == 0x240;
      var s5 := PushN(s4, 2, 0x0360);
      assert s5.stack[6] == 0x240;
      var s6 := Add(s5);
      assert s6.stack[5] == 0x240;
      var s7 := Add(s6);
      assert s7.stack[4] == 0x240;
      var s8 := MStore(s7);
      assert s8.stack[2] == 0x240;
      var s9 := PushN(s8, 1, 0x20);
      assert s9.stack[3] == 0x240;
      var s10 := Dup(s9, 2);
      assert s10.stack[4] == 0x240;
      var s11 := Add(s10);
      assert s11.stack[3] == 0x240;
      var s12 := Swap(s11, 1);
      assert s12.stack[3] == 0x240;
      var s13 := Pop(s12);
      assert s13.stack[2] == 0x240;
      var s14 := Dup(s13, 1);
      assert s14.stack[3] == 0x240;
      var s15 := PushN(s14, 2, 0x0360);
      assert s15.stack[4] == 0x240;
      var s16 := MStore(s15);
      assert s16.stack[2] == 0x240;
      var s17 := PushN(s16, 2, 0x0360);
      assert s17.stack[3] == 0x240;
      var s18 := Swap(s17, 1);
      assert s18.stack[3] == 0x240;
      var s19 := Pop(s18);
      assert s19.stack[2] == 0x240;
      var s20 := Dup(s19, 1);
      assert s20.stack[3] == 0x240;
      var s21 := MLoad(s20);
      assert s21.stack[3] == 0x240;
      var s22 := PushN(s21, 1, 0x20);
      assert s22.stack[4] == 0x240;
      var s23 := Add(s22);
      assert s23.stack[3] == 0x240;
      var s24 := Dup(s23, 1);
      assert s24.stack[4] == 0x240;
      var s25 := PushN(s24, 2, 0x0420);
      assert s25.stack[5] == 0x240;
      var s26 := Dup(s25, 3);
      assert s26.stack[6] == 0x240;
      var s27 := Dup(s26, 5);
      assert s27.stack[7] == 0x240;
      var s28 := PushN(s27, 1, 0x00);
      assert s28.stack[8] == 0x240;
      var s29 := PushN(s28, 1, 0x04);
      assert s29.stack[9] == 0x240;
      var s30 := Gas(s29);
      assert s30.stack[10] == 0x240;
      var s31 := Call(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s13(s31, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 16
    * Starting at 0x15d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := IsZero(s0);
      assert s1.stack[4] == 0x240;
      var s2 := PushN(s1, 2, 0x17ce);
      assert s2.stack[0] == 0x17ce;
      assert s2.stack[5] == 0x240;
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s3, gas - 1)
      else
        ExecuteFromCFGNode_s14(s3, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 17
    * Starting at 0x162
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x162 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0x240;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x240;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[2] == 0x240;
      var s4 := PushN(s3, 2, 0x0500);
      assert s4.stack[3] == 0x240;
      var s5 := PushN(s4, 2, 0x0420);
      assert s5.stack[4] == 0x240;
      var s6 := MLoad(s5);
      assert s6.stack[4] == 0x240;
      var s7 := PushN(s6, 2, 0x0440);
      assert s7.stack[5] == 0x240;
      var s8 := PushN(s7, 1, 0x00);
      assert s8.stack[6] == 0x240;
      var s9 := PushN(s8, 2, 0x0280);
      assert s9.stack[7] == 0x240;
      var s10 := MLoad(s9);
      assert s10.stack[7] == 0x240;
      var s11 := Gas(s10);
      assert s11.stack[8] == 0x240;
      var s12 := Call(s11);
      assert s12.stack[2] == 0x240;
      var s13 := IsZero(s12);
      assert s13.stack[2] == 0x240;
      var s14 := PushN(s13, 2, 0x17ce);
      assert s14.stack[0] == 0x17ce;
      assert s14.stack[3] == 0x240;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s15, gas - 1)
      else
        ExecuteFromCFGNode_s15(s15, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 18
    * Starting at 0x17d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[2] == 0x240;
      var s2 := ReturnDataSize(s1);
      assert s2.stack[3] == 0x240;
      var s3 := Dup(s2, 1);
      assert s3.stack[4] == 0x240;
      var s4 := Dup(s3, 3);
      assert s4.stack[5] == 0x240;
      var s5 := Gt(s4);
      assert s5.stack[4] == 0x240;
      var s6 := IsZero(s5);
      assert s6.stack[4] == 0x240;
      var s7 := PushN(s6, 2, 0x018d);
      assert s7.stack[0] == 0x18d;
      assert s7.stack[5] == 0x240;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s8, gas - 1)
      else
        ExecuteFromCFGNode_s16(s8, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 19
    * Starting at 0x188
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x188 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[4] == 0x240;
      var s2 := PushN(s1, 2, 0x018f);
      assert s2.stack[0] == 0x18f;
      assert s2.stack[5] == 0x240;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s3, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 21
    * Starting at 0x18f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x240;
      var s2 := Swap(s1, 1);
      assert s2.stack[4] == 0x240;
      var s3 := Pop(s2);
      assert s3.stack[3] == 0x240;
      var s4 := Swap(s3, 1);
      assert s4.stack[3] == 0x240;
      var s5 := Pop(s4);
      assert s5.stack[2] == 0x240;
      var s6 := PushN(s5, 2, 0x04e0);
      assert s6.stack[3] == 0x240;
      var s7 := MStore(s6);
      assert s7.stack[1] == 0x240;
      var s8 := PushN(s7, 2, 0x04e0);
      assert s8.stack[2] == 0x240;
      var s9 := Dup(s8, 1);
      assert s9.stack[3] == 0x240;
      var s10 := MLoad(s9);
      assert s10.stack[3] == 0x240;
      var s11 := PushN(s10, 1, 0x20);
      assert s11.stack[4] == 0x240;
      var s12 := Add(s11);
      assert s12.stack[3] == 0x240;
      var s13 := Dup(s12, 1);
      assert s13.stack[4] == 0x240;
      var s14 := PushN(s13, 2, 0x02a0);
      assert s14.stack[5] == 0x240;
      var s15 := Dup(s14, 3);
      assert s15.stack[6] == 0x240;
      var s16 := Dup(s15, 5);
      assert s16.stack[7] == 0x240;
      var s17 := PushN(s16, 1, 0x00);
      assert s17.stack[8] == 0x240;
      var s18 := PushN(s17, 1, 0x04);
      assert s18.stack[9] == 0x240;
      var s19 := Gas(s18);
      assert s19.stack[10] == 0x240;
      var s20 := Call(s19);
      assert s20.stack[4] == 0x240;
      var s21 := IsZero(s20);
      assert s21.stack[4] == 0x240;
      var s22 := PushN(s21, 2, 0x17ce);
      assert s22.stack[0] == 0x17ce;
      assert s22.stack[5] == 0x240;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s23, gas - 1)
      else
        ExecuteFromCFGNode_s18(s23, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 22
    * Starting at 0x1b1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x240

    decreases gas
  { 
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0x240;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x240;
      var s3 := PushN(s2, 1, 0x00);
      assert s3.stack[2] == 0x240;
      var s4 := PushN(s3, 2, 0x02a0);
      assert s4.stack[3] == 0x240;
      var s5 := MLoad(s4);
      assert s5.stack[3] == 0x240;
      var s6 := Xor(s5);
      assert s6.stack[2] == 0x240;
      var s7 := IsZero(s6);
      assert s7.stack[2] == 0x240;
      var s8 := PushN(s7, 2, 0x01f1);
      assert s8.stack[0] == 0x1f1;
      assert s8.stack[3] == 0x240;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s9, gas - 1)
      else
        ExecuteFromCFGNode_s19(s9, gas - 1)
  } 

  /** Node 19
    * Segment Id for this node is: 23
    * Starting at 0x1bf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x02a0);
      assert s1.stack[2] == 0x240;
      var s2 := Dup(s1, 1);
      assert s2.stack[3] == 0x240;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[4] == 0x240;
      var s4 := Add(s3);
      assert s4.stack[3] == 0x240;
      var s5 := MLoad(s4);
      assert s5.stack[3] == 0x240;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[4] == 0x240;
      var s7 := Dup(s6, 3);
      assert s7.stack[5] == 0x240;
      var s8 := MLoad(s7);
      assert s8.stack[5] == 0x240;
      var s9 := Dup(s8, 1);
      assert s9.stack[6] == 0x240;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[7] == 0x240;
      var s11 := Swap(s10, 1);
      assert s11.stack[7] == 0x240;
      var s12 := Sgt(s11);
      assert s12.stack[6] == 0x240;
      var s13 := PushN(s12, 2, 0x17ce);
      assert s13.stack[0] == 0x17ce;
      assert s13.stack[7] == 0x240;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s14, gas - 1)
      else
        ExecuteFromCFGNode_s20(s14, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 24
    * Starting at 0x1d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[6] == 0x240;
      var s2 := Swap(s1, 2);
      assert s2.stack[6] == 0x240;
      var s3 := Swap(s2, 1);
      assert s3.stack[6] == 0x240;
      var s4 := Slt(s3);
      assert s4.stack[5] == 0x240;
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      assert s5.stack[6] == 0x240;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s6, gas - 1)
      else
        ExecuteFromCFGNode_s21(s6, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 25
    * Starting at 0x1dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[5] == 0x240;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[6] == 0x240;
      var s3 := Sub(s2);
      assert s3.stack[5] == 0x240;
      var s4 := PushN(s3, 2, 0x0100);
      assert s4.stack[6] == 0x240;
      var s5 := Exp(s4);
      assert s5.stack[5] == 0x240;
      var s6 := Dup(s5, 3);
      assert s6.stack[6] == 0x240;
      var s7 := Div(s6);
      assert s7.stack[5] == 0x240;
      var s8 := Swap(s7, 1);
      assert s8.stack[5] == 0x240;
      var s9 := Pop(s8);
      assert s9.stack[4] == 0x240;
      var s10 := Swap(s9, 1);
      assert s10.stack[4] == 0x240;
      var s11 := Pop(s10);
      assert s11.stack[3] == 0x240;
      var s12 := Swap(s11, 1);
      assert s12.stack[3] == 0x240;
      var s13 := Pop(s12);
      assert s13.stack[2] == 0x240;
      var s14 := IsZero(s13);
      assert s14.stack[2] == 0x240;
      var s15 := PushN(s14, 2, 0x17ce);
      assert s15.stack[0] == 0x17ce;
      assert s15.stack[3] == 0x240;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s16, gas - 1)
      else
        ExecuteFromCFGNode_s22(s16, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 26
    * Starting at 0x1f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x240;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[2] == 0x240;
      var s3 := PushN(s2, 2, 0x0380);
      assert s3.stack[3] == 0x240;
      var s4 := PushN(s3, 1, 0x24);
      assert s4.stack[4] == 0x240;
      var s5 := PushN(s4, 4, 0x70a08231);
      assert s5.stack[5] == 0x240;
      var s6 := PushN(s5, 2, 0x0300);
      assert s6.stack[6] == 0x240;
      var s7 := MStore(s6);
      assert s7.stack[4] == 0x240;
      var s8 := Address(s7);
      assert s8.stack[5] == 0x240;
      var s9 := PushN(s8, 2, 0x0320);
      assert s9.stack[6] == 0x240;
      var s10 := MStore(s9);
      assert s10.stack[4] == 0x240;
      var s11 := PushN(s10, 2, 0x031c);
      assert s11.stack[5] == 0x240;
      var s12 := PushN(s11, 2, 0x0280);
      assert s12.stack[6] == 0x240;
      var s13 := MLoad(s12);
      assert s13.stack[6] == 0x240;
      var s14 := Gas(s13);
      assert s14.stack[7] == 0x240;
      var s15 := StaticCall(s14);
      assert s15.stack[2] == 0x240;
      var s16 := IsZero(s15);
      assert s16.stack[2] == 0x240;
      var s17 := PushN(s16, 2, 0x17ce);
      assert s17.stack[0] == 0x17ce;
      assert s17.stack[3] == 0x240;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s18, gas - 1)
      else
        ExecuteFromCFGNode_s23(s18, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 27
    * Starting at 0x215
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x215 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      assert s1.stack[2] == 0x240;
      var s2 := ReturnDataSize(s1);
      assert s2.stack[3] == 0x240;
      var s3 := Gt(s2);
      assert s3.stack[2] == 0x240;
      var s4 := IsZero(s3);
      assert s4.stack[2] == 0x240;
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      assert s5.stack[3] == 0x240;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s6, gas - 1)
      else
        ExecuteFromCFGNode_s24(s6, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 28
    * Starting at 0x21e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[2] == 0x240;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x240;
      var s3 := PushN(s2, 2, 0x0380);
      assert s3.stack[2] == 0x240;
      var s4 := MLoad(s3);
      assert s4.stack[2] == 0x240;
      var s5 := PushN(s4, 2, 0x0160);
      assert s5.stack[3] == 0x240;
      var s6 := PushN(s5, 2, 0x0240);
      assert s6.stack[0] == 0x240;
      assert s6.stack[4] == 0x240;
      var s7 := MLoad(s6);
      assert s7.stack[4] == 0x240;
      var s8 := PushN(s7, 1, 0x03);
      assert s8.stack[5] == 0x240;
      var s9 := Dup(s8, 2);
      assert s9.stack[6] == 0x240;
      var s10 := Lt(s9);
      assert s10.stack[5] == 0x240;
      var s11 := IsZero(s10);
      assert s11.stack[5] == 0x240;
      var s12 := PushN(s11, 2, 0x17ce);
      assert s12.stack[0] == 0x17ce;
      assert s12.stack[6] == 0x240;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s13, gas - 1)
      else
        ExecuteFromCFGNode_s25(s13, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 29
    * Starting at 0x235
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x235 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[5] == 0x240;
      var s2 := Mul(s1);
      assert s2.stack[4] == 0x240;
      var s3 := Add(s2);
      assert s3.stack[3] == 0x240;
      var s4 := MStore(s3);
      assert s4.stack[1] == 0x240;
      var s5 := PushN(s4, 1, 0x01);
      assert s5.stack[2] == 0x240;
      var s6 := PushN(s5, 2, 0x0220);
      assert s6.stack[3] == 0x240;
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s26(s7, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 30
    * Starting at 0x240
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x240 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s27(s1, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 31
    * Starting at 0x241
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x241 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x240;
      var s2 := Dup(s1, 2);
      assert s2.stack[0] == 0x240;
      assert s2.stack[2] == 0x240;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x240;
      var s4 := PushN(s3, 1, 0x01);
      assert s4.stack[3] == 0x240;
      var s5 := Add(s4);
      assert s5.stack[2] == 0x240;
      var s6 := Dup(s5, 1);
      assert s6.stack[3] == 0x240;
      var s7 := Dup(s6, 4);
      assert s7.stack[0] == 0x240;
      assert s7.stack[4] == 0x240;
      var s8 := MStore(s7);
      assert s8.stack[2] == 0x240;
      var s9 := Dup(s8, 2);
      assert s9.stack[3] == 0x240;
      var s10 := Eq(s9);
      assert s10.stack[2] == 0x240;
      var s11 := IsZero(s10);
      assert s11.stack[2] == 0x240;
      var s12 := PushN(s11, 2, 0x0083);
      assert s12.stack[0] == 0x83;
      assert s12.stack[3] == 0x240;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s7(s13, gas - 1)
      else
        ExecuteFromCFGNode_s28(s13, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 32
    * Starting at 0x251
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x251 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x240;
      var s2 := Pop(s1);
      assert s2.stack[0] == 0x240;
      var s3 := Pop(s2);
      var s4 := PushN(s3, 2, 0x0220);
      var s5 := MLoad(s4);
      var s6 := IsZero(s5);
      var s7 := PushN(s6, 2, 0x02b4);
      assert s7.stack[0] == 0x2b4;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s8, gas - 1)
      else
        ExecuteFromCFGNode_s29(s8, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 33
    * Starting at 0x25d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 2, 0x0340);
      var s3 := PushN(s2, 1, 0xa4);
      var s4 := PushN(s3, 4, 0x2b6e993a);
      var s5 := PushN(s4, 2, 0x0240);
      assert s5.stack[0] == 0x240;
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0160);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x0260);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0180);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x0280);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 2, 0x01a0);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 2, 0x02a0);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 1, 0x00);
      var s20 := PushN(s19, 2, 0x02c0);
      var s21 := MStore(s20);
      var s22 := PushN(s21, 1, 0x01);
      var s23 := PushN(s22, 2, 0x02e0);
      var s24 := MStore(s23);
      var s25 := PushN(s24, 2, 0x025c);
      var s26 := PushN(s25, 1, 0x00);
      var s27 := PushN(s26, 1, 0x0a);
      var s28 := SLoad(s27);
      var s29 := Gas(s28);
      var s30 := Call(s29);
      var s31 := IsZero(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s30(s31, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 34
    * Starting at 0x29c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x17ce);
      assert s1.stack[0] == 0x17ce;
      var s2 := JumpI(s1);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s1.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s2, gas - 1)
      else
        ExecuteFromCFGNode_s31(s2, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 35
    * Starting at 0x2a0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s32(s6, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 36
    * Starting at 0x2a9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0340);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x01c0);
      var s6 := MStore(s5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s33(s6, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 37
    * Starting at 0x2b4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := SLoad(s2);
      var s4 := PushN(s3, 2, 0x0240);
      assert s4.stack[0] == 0x240;
      var s5 := MStore(s4);
      var s6 := PushN(s5, 2, 0x0260);
      var s7 := PushN(s6, 1, 0x03);
      var s8 := PushN(s7, 1, 0x02);
      var s9 := Dup(s8, 2);
      var s10 := Dup(s9, 4);
      var s11 := MStore(s10);
      var s12 := Add(s11);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s34(s12, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 38
    * Starting at 0x2c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := PushN(s2, 2, 0x0260);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x05);
      var s6 := Dup(s5, 2);
      var s7 := Lt(s6);
      var s8 := IsZero(s7);
      var s9 := PushN(s8, 2, 0x17ce);
      assert s9.stack[0] == 0x17ce;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s10, gas - 1)
      else
        ExecuteFromCFGNode_s35(s10, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 39
    * Starting at 0x2d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := Mul(s1);
      var s3 := Add(s2);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 2, 0x0280);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 2, 0x0280);
      var s9 := MLoad(s8);
      var s10 := Xor(s9);
      var s11 := IsZero(s10);
      var s12 := PushN(s11, 2, 0x0542);
      assert s12.stack[0] == 0x542;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s13, gas - 1)
      else
        ExecuteFromCFGNode_s36(s13, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 40
    * Starting at 0x2ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x01);
      var s2 := PushN(s1, 2, 0x0260);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x05);
      var s5 := Dup(s4, 2);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s9, gas - 1)
      else
        ExecuteFromCFGNode_s37(s9, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 41
    * Starting at 0x2fb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 2, 0x02a0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 1, 0x04);
      var s9 := PushN(s8, 2, 0x0320);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 32, 0x23b872dd00000000000000000000000000000000000000000000000000000000);
      var s12 := PushN(s11, 2, 0x0340);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 2, 0x0320);
      var s15 := PushN(s14, 1, 0x04);
      var s16 := Dup(s15, 1);
      var s17 := PushN(s16, 1, 0x20);
      var s18 := Dup(s17, 5);
      var s19 := PushN(s18, 2, 0x0380);
      var s20 := Add(s19);
      var s21 := Add(s20);
      var s22 := Dup(s21, 3);
      var s23 := PushN(s22, 1, 0x20);
      var s24 := Dup(s23, 6);
      var s25 := Add(s24);
      var s26 := PushN(s25, 1, 0x00);
      var s27 := PushN(s26, 1, 0x04);
      var s28 := Gas(s27);
      var s29 := Call(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s38(s31, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 42
    * Starting at 0x34c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := MLoad(s1);
      var s3 := Dup(s2, 3);
      var s4 := Add(s3);
      var s5 := Swap(s4, 2);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Caller(s7);
      var s9 := PushN(s8, 1, 0x20);
      var s10 := Dup(s9, 3);
      var s11 := PushN(s10, 2, 0x0380);
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 1, 0x20);
      var s16 := Dup(s15, 2);
      var s17 := Add(s16);
      var s18 := Swap(s17, 1);
      var s19 := Pop(s18);
      var s20 := Address(s19);
      var s21 := PushN(s20, 1, 0x20);
      var s22 := Dup(s21, 3);
      var s23 := PushN(s22, 2, 0x0380);
      var s24 := Add(s23);
      var s25 := Add(s24);
      var s26 := MStore(s25);
      var s27 := PushN(s26, 1, 0x20);
      var s28 := Dup(s27, 2);
      var s29 := Add(s28);
      var s30 := Swap(s29, 1);
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s39(s31, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 43
    * Starting at 0x373
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x373 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0280);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := Dup(s3, 3);
      var s5 := PushN(s4, 2, 0x0380);
      var s6 := Add(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x20);
      var s10 := Dup(s9, 2);
      var s11 := Add(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Dup(s13, 1);
      var s15 := PushN(s14, 2, 0x0380);
      var s16 := MStore(s15);
      var s17 := PushN(s16, 2, 0x0380);
      var s18 := Swap(s17, 1);
      var s19 := Pop(s18);
      var s20 := Dup(s19, 1);
      var s21 := MLoad(s20);
      var s22 := PushN(s21, 1, 0x20);
      var s23 := Add(s22);
      var s24 := Dup(s23, 1);
      var s25 := PushN(s24, 2, 0x0440);
      var s26 := Dup(s25, 3);
      var s27 := Dup(s26, 5);
      var s28 := PushN(s27, 1, 0x00);
      var s29 := PushN(s28, 1, 0x04);
      var s30 := Gas(s29);
      var s31 := Call(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s40(s31, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 44
    * Starting at 0x3a1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := IsZero(s0);
      var s2 := PushN(s1, 2, 0x17ce);
      assert s2.stack[0] == 0x17ce;
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s3, gas - 1)
      else
        ExecuteFromCFGNode_s41(s3, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 45
    * Starting at 0x3a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x0520);
      var s5 := PushN(s4, 2, 0x0440);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0460);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 2, 0x02a0);
      var s10 := MLoad(s9);
      var s11 := Gas(s10);
      var s12 := Call(s11);
      var s13 := IsZero(s12);
      var s14 := PushN(s13, 2, 0x17ce);
      assert s14.stack[0] == 0x17ce;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s15, gas - 1)
      else
        ExecuteFromCFGNode_s42(s15, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 46
    * Starting at 0x3c1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := ReturnDataSize(s1);
      var s3 := Dup(s2, 1);
      var s4 := Dup(s3, 3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := PushN(s6, 2, 0x03d1);
      assert s7.stack[0] == 0x3d1;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s8, gas - 1)
      else
        ExecuteFromCFGNode_s43(s8, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 47
    * Starting at 0x3cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 2, 0x03d3);
      assert s2.stack[0] == 0x3d3;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s3, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 49
    * Starting at 0x3d3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := PushN(s5, 2, 0x0500);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x0500);
      var s9 := Dup(s8, 1);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Add(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x02c0);
      var s15 := Dup(s14, 3);
      var s16 := Dup(s15, 5);
      var s17 := PushN(s16, 1, 0x00);
      var s18 := PushN(s17, 1, 0x04);
      var s19 := Gas(s18);
      var s20 := Call(s19);
      var s21 := IsZero(s20);
      var s22 := PushN(s21, 2, 0x17ce);
      assert s22.stack[0] == 0x17ce;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s23, gas - 1)
      else
        ExecuteFromCFGNode_s45(s23, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 50
    * Starting at 0x3f5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 2, 0x02c0);
      var s5 := MLoad(s4);
      var s6 := Xor(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x0435);
      assert s8.stack[0] == 0x435;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s9, gas - 1)
      else
        ExecuteFromCFGNode_s46(s9, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 51
    * Starting at 0x403
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x403 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x02c0);
      var s2 := Dup(s1, 1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Dup(s6, 3);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Swap(s10, 1);
      var s12 := Sgt(s11);
      var s13 := PushN(s12, 2, 0x17ce);
      assert s13.stack[0] == 0x17ce;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s14, gas - 1)
      else
        ExecuteFromCFGNode_s47(s14, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 52
    * Starting at 0x418
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Swap(s1, 2);
      var s3 := Swap(s2, 1);
      var s4 := Slt(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s6, gas - 1)
      else
        ExecuteFromCFGNode_s48(s6, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 53
    * Starting at 0x420
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x420 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := Sub(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := Exp(s4);
      var s6 := Dup(s5, 3);
      var s7 := Div(s6);
      var s8 := Swap(s7, 1);
      var s9 := Pop(s8);
      var s10 := Swap(s9, 1);
      var s11 := Pop(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := IsZero(s13);
      var s15 := PushN(s14, 2, 0x17ce);
      assert s15.stack[0] == 0x17ce;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s16, gas - 1)
      else
        ExecuteFromCFGNode_s49(s16, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 54
    * Starting at 0x435
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x435 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := PushN(s3, 2, 0x0320);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 32, 0xe8eda9df00000000000000000000000000000000000000000000000000000000);
      var s7 := PushN(s6, 2, 0x0340);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0320);
      var s10 := PushN(s9, 1, 0x04);
      var s11 := Dup(s10, 1);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Dup(s12, 5);
      var s14 := PushN(s13, 2, 0x0380);
      var s15 := Add(s14);
      var s16 := Add(s15);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 6);
      var s20 := Add(s19);
      var s21 := PushN(s20, 1, 0x00);
      var s22 := PushN(s21, 1, 0x04);
      var s23 := Gas(s22);
      var s24 := Call(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Dup(s26, 1);
      var s28 := MLoad(s27);
      var s29 := Dup(s28, 3);
      var s30 := Add(s29);
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s50(s31, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 55
    * Starting at 0x483
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x483 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x02a0);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := Dup(s5, 3);
      var s7 := PushN(s6, 2, 0x0380);
      var s8 := Add(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Dup(s11, 2);
      var s13 := Add(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := PushN(s15, 2, 0x0280);
      var s17 := MLoad(s16);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 3);
      var s20 := PushN(s19, 2, 0x0380);
      var s21 := Add(s20);
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := PushN(s23, 1, 0x20);
      var s25 := Dup(s24, 2);
      var s26 := Add(s25);
      var s27 := Swap(s26, 1);
      var s28 := Pop(s27);
      var s29 := Address(s28);
      var s30 := PushN(s29, 1, 0x20);
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s51(s31, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 56
    * Starting at 0x4af
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0380);
      var s2 := Add(s1);
      var s3 := Add(s2);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := Dup(s5, 2);
      var s7 := Add(s6);
      var s8 := Swap(s7, 1);
      var s9 := Pop(s8);
      var s10 := PushN(s9, 2, 0x0240);
      assert s10.stack[0] == 0x240;
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Dup(s12, 3);
      var s14 := PushN(s13, 2, 0x0380);
      var s15 := Add(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 2);
      var s20 := Add(s19);
      var s21 := Swap(s20, 1);
      var s22 := Pop(s21);
      var s23 := Dup(s22, 1);
      var s24 := PushN(s23, 2, 0x0380);
      var s25 := MStore(s24);
      var s26 := PushN(s25, 2, 0x0380);
      var s27 := Swap(s26, 1);
      var s28 := Pop(s27);
      var s29 := Dup(s28, 1);
      var s30 := MLoad(s29);
      var s31 := PushN(s30, 1, 0x20);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s52(s31, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 57
    * Starting at 0x4dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      var s2 := Dup(s1, 1);
      var s3 := PushN(s2, 2, 0x0460);
      var s4 := Dup(s3, 3);
      var s5 := Dup(s4, 5);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := PushN(s6, 1, 0x04);
      var s8 := Gas(s7);
      var s9 := Call(s8);
      var s10 := IsZero(s9);
      var s11 := PushN(s10, 2, 0x17ce);
      assert s11.stack[0] == 0x17ce;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s12, gas - 1)
      else
        ExecuteFromCFGNode_s53(s12, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 58
    * Starting at 0x4ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 1, 0x00);
      var s5 := PushN(s4, 2, 0x0460);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0480);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 20, 0x4f01aed16d97e3ab5ab2b501154dc9bb0f1a5a2c);
      var s10 := Gas(s9);
      var s11 := Call(s10);
      var s12 := IsZero(s11);
      var s13 := PushN(s12, 2, 0x17ce);
      assert s13.stack[0] == 0x17ce;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s14, gas - 1)
      else
        ExecuteFromCFGNode_s54(s14, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 59
    * Starting at 0x519
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x519 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0280);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x01c0);
      var s4 := PushN(s3, 2, 0x0260);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 1, 0x02);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 3);
      var s9 := Lt(s8);
      var s10 := PushN(s9, 2, 0x17ce);
      assert s10.stack[0] == 0x17ce;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s11, gas - 1)
      else
        ExecuteFromCFGNode_s55(s11, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 60
    * Starting at 0x52d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52d as nat
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
      var s12 := PushN(s11, 2, 0x17ce);
      assert s12.stack[0] == 0x17ce;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s13, gas - 1)
      else
        ExecuteFromCFGNode_s56(s13, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 61
    * Starting at 0x53d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53d as nat
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
      ExecuteFromCFGNode_s57(s4, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 62
    * Starting at 0x542
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x542 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s58(s1, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 63
    * Starting at 0x543
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x543 as nat
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
      var s12 := PushN(s11, 2, 0x02c7);
      assert s12.stack[0] == 0x2c7;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s13, gas - 1)
      else
        ExecuteFromCFGNode_s59(s13, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 64
    * Starting at 0x553
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x553 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := PushN(s3, 1, 0x09);
      var s5 := SLoad(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s9, gas - 1)
      else
        ExecuteFromCFGNode_s60(s9, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 65
    * Starting at 0x55f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x84);
      var s4 := PushN(s3, 4, 0x4515cef3);
      var s5 := PushN(s4, 2, 0x0260);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x01c0);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x0280);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x01e0);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x02a0);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 2, 0x0200);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 2, 0x02c0);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 1, 0xa4);
      var s20 := CallDataLoad(s19);
      var s21 := PushN(s20, 2, 0x02e0);
      var s22 := MStore(s21);
      var s23 := PushN(s22, 2, 0x027c);
      var s24 := PushN(s23, 1, 0x00);
      var s25 := PushN(s24, 1, 0x09);
      var s26 := SLoad(s25);
      var s27 := Gas(s26);
      var s28 := Call(s27);
      var s29 := IsZero(s28);
      var s30 := PushN(s29, 2, 0x17ce);
      assert s30.stack[0] == 0x17ce;
      var s31 := JumpI(s30);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s30.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s31, gas - 1)
      else
        ExecuteFromCFGNode_s61(s31, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 66
    * Starting at 0x59c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x0b);
      var s2 := SLoad(s1);
      var s3 := PushN(s2, 2, 0x0260);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x0320);
      var s7 := PushN(s6, 1, 0x24);
      var s8 := PushN(s7, 4, 0x70a08231);
      var s9 := PushN(s8, 2, 0x02a0);
      var s10 := MStore(s9);
      var s11 := Address(s10);
      var s12 := PushN(s11, 2, 0x02c0);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 2, 0x02bc);
      var s15 := PushN(s14, 2, 0x0260);
      var s16 := MLoad(s15);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := IsZero(s18);
      var s20 := PushN(s19, 2, 0x17ce);
      assert s20.stack[0] == 0x17ce;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s21, gas - 1)
      else
        ExecuteFromCFGNode_s62(s21, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 67
    * Starting at 0x5c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s63(s6, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 68
    * Starting at 0x5cf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0320);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0280);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 2, 0x0340);
      var s9 := PushN(s8, 1, 0x44);
      var s10 := PushN(s9, 4, 0xa9059cbb);
      var s11 := PushN(s10, 2, 0x02a0);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 2, 0x0140);
      var s14 := MLoad(s13);
      var s15 := PushN(s14, 2, 0x02c0);
      var s16 := MStore(s15);
      var s17 := PushN(s16, 2, 0x0280);
      var s18 := MLoad(s17);
      var s19 := PushN(s18, 2, 0x02e0);
      var s20 := MStore(s19);
      var s21 := PushN(s20, 2, 0x02bc);
      var s22 := PushN(s21, 1, 0x00);
      var s23 := PushN(s22, 2, 0x0260);
      var s24 := MLoad(s23);
      var s25 := Gas(s24);
      var s26 := Call(s25);
      var s27 := IsZero(s26);
      var s28 := PushN(s27, 2, 0x17ce);
      assert s28.stack[0] == 0x17ce;
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s29, gas - 1)
      else
        ExecuteFromCFGNode_s64(s29, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 69
    * Starting at 0x60a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s65(s6, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 70
    * Starting at 0x613
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x613 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0340);
      var s4 := Pop(s3);
      var s5 := Stop(s4);
      // Segment is terminal (Revert, Stop or Return)
      s5
  }

  /** Node 66
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
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

  /** Node 67
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
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

  /** Node 68
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
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

  /** Node 69
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
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

  /** Node 70
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
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

  /** Node 71
    * Segment Id for this node is: 48
    * Starting at 0x3d1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s44(s2, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x240;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[5] == 0x240;
      var s3 := Dup(s2, 1);
      assert s3.stack[6] == 0x240;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 73
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x240;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[2] == 0x240;
      var s3 := Dup(s2, 1);
      assert s3.stack[3] == 0x240;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 74
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x240;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[6] == 0x240;
      var s3 := Dup(s2, 1);
      assert s3.stack[7] == 0x240;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 75
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x240;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[4] == 0x240;
      var s3 := Dup(s2, 1);
      assert s3.stack[5] == 0x240;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 76
    * Segment Id for this node is: 20
    * Starting at 0x18d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x240;
      var s2 := Dup(s1, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s17(s2, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 5
    * Starting at 0x45
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xcf2b51b8);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x006b);
      assert s6.stack[0] == 0x6b;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s80(s7, gas - 1)
      else
        ExecuteFromCFGNode_s78(s7, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 6
    * Starting at 0x52
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xc4);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0xa0);
      var s4 := Shr(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s79(s6, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 7
    * Starting at 0x5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 1, 0xc4);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := CallDataCopy(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0070);
      assert s7.stack[0] == 0x70;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s6(s8, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 8
    * Starting at 0x6b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x061b);
      assert s2.stack[0] == 0x61b;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s3, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 71
    * Starting at 0x61b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x65b2489b);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x0631);
      assert s6.stack[0] == 0x631;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s146(s7, gas - 1)
      else
        ExecuteFromCFGNode_s82(s7, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 72
    * Starting at 0x628
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x628 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 2, 0x0140);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x065c);
      assert s4.stack[0] == 0x65c;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s5, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 77
    * Starting at 0x65c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65c as nat
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
      var s6 := PushN(s5, 32, 0x23b872dd00000000000000000000000000000000000000000000000000000000);
      var s7 := PushN(s6, 2, 0x01e0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x01c0);
      var s10 := PushN(s9, 1, 0x04);
      var s11 := Dup(s10, 1);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Dup(s12, 5);
      var s14 := PushN(s13, 2, 0x0220);
      var s15 := Add(s14);
      var s16 := Add(s15);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 6);
      var s20 := Add(s19);
      var s21 := PushN(s20, 1, 0x00);
      var s22 := PushN(s21, 1, 0x04);
      var s23 := Gas(s22);
      var s24 := Call(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Dup(s26, 1);
      var s28 := MLoad(s27);
      var s29 := Dup(s28, 3);
      var s30 := Add(s29);
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s84(s31, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 78
    * Starting at 0x6aa
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Caller(s2);
      var s4 := PushN(s3, 1, 0x20);
      var s5 := Dup(s4, 3);
      var s6 := PushN(s5, 2, 0x0220);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Dup(s10, 2);
      var s12 := Add(s11);
      var s13 := Swap(s12, 1);
      var s14 := Pop(s13);
      var s15 := Address(s14);
      var s16 := PushN(s15, 1, 0x20);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 2, 0x0220);
      var s19 := Add(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      var s22 := PushN(s21, 1, 0x20);
      var s23 := Dup(s22, 2);
      var s24 := Add(s23);
      var s25 := Swap(s24, 1);
      var s26 := Pop(s25);
      var s27 := PushN(s26, 1, 0x44);
      var s28 := CallDataLoad(s27);
      var s29 := PushN(s28, 1, 0x20);
      var s30 := Dup(s29, 3);
      var s31 := PushN(s30, 2, 0x0220);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s85(s31, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 79
    * Starting at 0x6d5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      var s2 := Add(s1);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 1, 0x20);
      var s5 := Dup(s4, 2);
      var s6 := Add(s5);
      var s7 := Swap(s6, 1);
      var s8 := Pop(s7);
      var s9 := Dup(s8, 1);
      var s10 := PushN(s9, 2, 0x0220);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x0220);
      var s13 := Swap(s12, 1);
      var s14 := Pop(s13);
      var s15 := Dup(s14, 1);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 1, 0x20);
      var s18 := Add(s17);
      var s19 := Dup(s18, 1);
      var s20 := PushN(s19, 2, 0x02e0);
      var s21 := Dup(s20, 3);
      var s22 := Dup(s21, 5);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 1, 0x04);
      var s25 := Gas(s24);
      var s26 := Call(s25);
      var s27 := IsZero(s26);
      var s28 := PushN(s27, 2, 0x17ce);
      assert s28.stack[0] == 0x17ce;
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s29, gas - 1)
      else
        ExecuteFromCFGNode_s86(s29, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 80
    * Starting at 0x6fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x03c0);
      var s5 := PushN(s4, 2, 0x02e0);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0300);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 1, 0x01);
      var s10 := PushN(s9, 1, 0x04);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 1, 0x05);
      var s13 := Dup(s12, 2);
      var s14 := Lt(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x17ce);
      assert s16.stack[0] == 0x17ce;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s17, gas - 1)
      else
        ExecuteFromCFGNode_s87(s17, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 81
    * Starting at 0x71c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s9, gas - 1)
      else
        ExecuteFromCFGNode_s88(s9, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 82
    * Starting at 0x728
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x728 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := ReturnDataSize(s1);
      var s3 := Dup(s2, 1);
      var s4 := Dup(s3, 3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := PushN(s6, 2, 0x0738);
      assert s7.stack[0] == 0x738;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s8, gas - 1)
      else
        ExecuteFromCFGNode_s89(s8, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 83
    * Starting at 0x733
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x733 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 2, 0x073a);
      assert s2.stack[0] == 0x73a;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s3, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 85
    * Starting at 0x73a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := PushN(s5, 2, 0x03a0);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x03a0);
      var s9 := Dup(s8, 1);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Add(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x0160);
      var s15 := Dup(s14, 3);
      var s16 := Dup(s15, 5);
      var s17 := PushN(s16, 1, 0x00);
      var s18 := PushN(s17, 1, 0x04);
      var s19 := Gas(s18);
      var s20 := Call(s19);
      var s21 := IsZero(s20);
      var s22 := PushN(s21, 2, 0x17ce);
      assert s22.stack[0] == 0x17ce;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s23, gas - 1)
      else
        ExecuteFromCFGNode_s91(s23, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 86
    * Starting at 0x75c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 2, 0x0160);
      var s5 := MLoad(s4);
      var s6 := Xor(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x079c);
      assert s8.stack[0] == 0x79c;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s9, gas - 1)
      else
        ExecuteFromCFGNode_s92(s9, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 87
    * Starting at 0x76a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0160);
      var s2 := Dup(s1, 1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Dup(s6, 3);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Swap(s10, 1);
      var s12 := Sgt(s11);
      var s13 := PushN(s12, 2, 0x17ce);
      assert s13.stack[0] == 0x17ce;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s14, gas - 1)
      else
        ExecuteFromCFGNode_s93(s14, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 88
    * Starting at 0x77f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Swap(s1, 2);
      var s3 := Swap(s2, 1);
      var s4 := Slt(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s6, gas - 1)
      else
        ExecuteFromCFGNode_s94(s6, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 89
    * Starting at 0x787
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x787 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := Sub(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := Exp(s4);
      var s6 := Dup(s5, 3);
      var s7 := Div(s6);
      var s8 := Swap(s7, 1);
      var s9 := Pop(s8);
      var s10 := Swap(s9, 1);
      var s11 := Pop(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := IsZero(s13);
      var s15 := PushN(s14, 2, 0x17ce);
      assert s15.stack[0] == 0x17ce;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s16, gas - 1)
      else
        ExecuteFromCFGNode_s95(s16, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 90
    * Starting at 0x79c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x44);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 2, 0x01c0);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x40);
      var s7 := CallDataSize(s6);
      var s8 := PushN(s7, 2, 0x01e0);
      var s9 := CallDataCopy(s8);
      var s10 := PushN(s9, 1, 0x03);
      var s11 := PushN(s10, 1, 0x24);
      var s12 := CallDataLoad(s11);
      var s13 := Lt(s12);
      var s14 := PushN(s13, 2, 0x07cc);
      assert s14.stack[0] == 0x7cc;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s15, gas - 1)
      else
        ExecuteFromCFGNode_s96(s15, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 91
    * Starting at 0x7b5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b5 as nat
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
      var s7 := PushN(s6, 2, 0x17ce);
      assert s7.stack[0] == 0x17ce;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s8, gas - 1)
      else
        ExecuteFromCFGNode_s97(s8, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 92
    * Starting at 0x7c1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c1 as nat
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
      var s8 := PushN(s7, 2, 0x0200);
      var s9 := MStore(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s98(s9, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 93
    * Starting at 0x7cc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cc as nat
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
      var s6 := IsZero(s5);
      var s7 := PushN(s6, 2, 0x0852);
      assert s7.stack[0] == 0x852;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s138(s8, gas - 1)
      else
        ExecuteFromCFGNode_s99(s8, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 94
    * Starting at 0x7d8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x60);
      var s2 := CallDataSize(s1);
      var s3 := PushN(s2, 2, 0x0220);
      var s4 := CallDataCopy(s3);
      var s5 := PushN(s4, 2, 0x01c0);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0220);
      var s8 := PushN(s7, 1, 0x04);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 1, 0x03);
      var s11 := Dup(s10, 2);
      var s12 := Lt(s11);
      var s13 := IsZero(s12);
      var s14 := PushN(s13, 2, 0x17ce);
      assert s14.stack[0] == 0x17ce;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s15, gas - 1)
      else
        ExecuteFromCFGNode_s100(s15, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 95
    * Starting at 0x7f2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f2 as nat
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
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x0380);
      var s7 := PushN(s6, 1, 0xa4);
      var s8 := PushN(s7, 4, 0x2b6e993a);
      var s9 := PushN(s8, 2, 0x0280);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0220);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x02a0);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 2, 0x0240);
      assert s15.stack[0] == 0x240;
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 2, 0x02c0);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 2, 0x0260);
      var s20 := MLoad(s19);
      var s21 := PushN(s20, 2, 0x02e0);
      var s22 := MStore(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0300);
      var s25 := MStore(s24);
      var s26 := PushN(s25, 1, 0x01);
      var s27 := PushN(s26, 2, 0x0320);
      var s28 := MStore(s27);
      var s29 := PushN(s28, 2, 0x029c);
      var s30 := PushN(s29, 1, 0x00);
      var s31 := PushN(s30, 1, 0x0a);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s101(s31, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 96
    * Starting at 0x832
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x832 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := SLoad(s0);
      var s2 := Gas(s1);
      var s3 := Call(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s102(s6, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 97
    * Starting at 0x83a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s103(s6, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 98
    * Starting at 0x843
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x843 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0380);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x01c0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x095b);
      assert s7.stack[0] == 0x95b;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s8, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 106
    * Starting at 0x95b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 2, 0x01e0);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0200);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 3);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := PushN(s10, 2, 0x0973);
      assert s11.stack[0] == 0x973;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s12, gas - 1)
      else
        ExecuteFromCFGNode_s105(s12, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 107
    * Starting at 0x96e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 2, 0x0975);
      assert s2.stack[0] == 0x975;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s3, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 109
    * Starting at 0x975
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x975 as nat
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
      var s8 := PushN(s7, 2, 0x09c5);
      assert s8.stack[0] == 0x9c5;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s109(s9, gas - 1)
      else
        ExecuteFromCFGNode_s107(s9, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 110
    * Starting at 0x980
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x980 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x09);
      var s2 := SLoad(s1);
      var s3 := ExtCodeSize(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s108(s6, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 111
    * Starting at 0x989
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x989 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x84);
      var s4 := PushN(s3, 4, 0x5b41b908);
      var s5 := PushN(s4, 2, 0x0220);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x01e0);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x0240);
      assert s9.stack[0] == 0x240;
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0200);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x0260);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 2, 0x01c0);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 2, 0x0280);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 1, 0x00);
      var s20 := PushN(s19, 2, 0x02a0);
      var s21 := MStore(s20);
      var s22 := PushN(s21, 2, 0x023c);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 1, 0x09);
      var s25 := SLoad(s24);
      var s26 := Gas(s25);
      var s27 := Call(s26);
      var s28 := IsZero(s27);
      var s29 := PushN(s28, 2, 0x17ce);
      assert s29.stack[0] == 0x17ce;
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s30, gas - 1)
      else
        ExecuteFromCFGNode_s109(s30, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 112
    * Starting at 0x9c5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x02c0);
      var s4 := PushN(s3, 1, 0x24);
      var s5 := PushN(s4, 4, 0x70a08231);
      var s6 := PushN(s5, 2, 0x0240);
      assert s6.stack[0] == 0x240;
      var s7 := MStore(s6);
      var s8 := Address(s7);
      var s9 := PushN(s8, 2, 0x0260);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x025c);
      var s12 := PushN(s11, 1, 0x01);
      var s13 := PushN(s12, 2, 0x0200);
      var s14 := MLoad(s13);
      var s15 := PushN(s14, 1, 0x03);
      var s16 := Dup(s15, 2);
      var s17 := Lt(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x17ce);
      assert s19.stack[0] == 0x17ce;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s20, gas - 1)
      else
        ExecuteFromCFGNode_s110(s20, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 113
    * Starting at 0x9ed
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x01);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := StaticCall(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s9, gas - 1)
      else
        ExecuteFromCFGNode_s111(s9, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 114
    * Starting at 0x9f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s112(s6, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 115
    * Starting at 0xa02
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x02c0);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0220);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0200);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x0ba5);
      assert s9.stack[0] == 0xba5;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s10, gas - 1)
      else
        ExecuteFromCFGNode_s113(s10, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 116
    * Starting at 0xa15
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa15 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 2, 0x0320);
      var s3 := PushN(s2, 1, 0x84);
      var s4 := PushN(s3, 4, 0x517a55a3);
      var s5 := PushN(s4, 2, 0x0240);
      assert s5.stack[0] == 0x240;
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0220);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x0260);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x24);
      var s12 := CallDataLoad(s11);
      var s13 := PushN(s12, 1, 0x40);
      var s14 := MLoad(s13);
      var s15 := Dup(s14, 2);
      var s16 := Gt(s15);
      var s17 := PushN(s16, 2, 0x17ce);
      assert s17.stack[0] == 0x17ce;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s18, gas - 1)
      else
        ExecuteFromCFGNode_s114(s18, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 117
    * Starting at 0xa39
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0280);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x64);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 2, 0x02a0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x01);
      var s8 := PushN(s7, 2, 0x02c0);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x025c);
      var s11 := PushN(s10, 1, 0x00);
      var s12 := PushN(s11, 1, 0x0a);
      var s13 := SLoad(s12);
      var s14 := Gas(s13);
      var s15 := Call(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x17ce);
      assert s17.stack[0] == 0x17ce;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s18, gas - 1)
      else
        ExecuteFromCFGNode_s115(s18, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 118
    * Starting at 0xa59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s116(s6, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 119
    * Starting at 0xa62
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0320);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0220);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 1, 0x04);
      var s9 := PushN(s8, 2, 0x0240);
      assert s9.stack[0] == 0x240;
      var s10 := MStore(s9);
      var s11 := PushN(s10, 32, 0xa9059cbb00000000000000000000000000000000000000000000000000000000);
      var s12 := PushN(s11, 2, 0x0260);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 2, 0x0240);
      assert s14.stack[0] == 0x240;
      var s15 := PushN(s14, 1, 0x04);
      assert s15.stack[1] == 0x240;
      var s16 := Dup(s15, 1);
      assert s16.stack[2] == 0x240;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[3] == 0x240;
      var s18 := Dup(s17, 5);
      assert s18.stack[4] == 0x240;
      var s19 := PushN(s18, 2, 0x02a0);
      assert s19.stack[5] == 0x240;
      var s20 := Add(s19);
      assert s20.stack[4] == 0x240;
      var s21 := Add(s20);
      assert s21.stack[3] == 0x240;
      var s22 := Dup(s21, 3);
      assert s22.stack[4] == 0x240;
      var s23 := PushN(s22, 1, 0x20);
      assert s23.stack[5] == 0x240;
      var s24 := Dup(s23, 6);
      assert s24.stack[0] == 0x240;
      assert s24.stack[6] == 0x240;
      var s25 := Add(s24);
      assert s25.stack[5] == 0x240;
      var s26 := PushN(s25, 1, 0x00);
      assert s26.stack[6] == 0x240;
      var s27 := PushN(s26, 1, 0x04);
      assert s27.stack[7] == 0x240;
      var s28 := Gas(s27);
      assert s28.stack[8] == 0x240;
      var s29 := Call(s28);
      assert s29.stack[2] == 0x240;
      var s30 := Pop(s29);
      assert s30.stack[1] == 0x240;
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s117(s31, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 120
    * Starting at 0xab5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[0] == 0x240;
      assert s1.stack[1] == 0x240;
      var s2 := MLoad(s1);
      assert s2.stack[1] == 0x240;
      var s3 := Dup(s2, 3);
      assert s3.stack[2] == 0x240;
      var s4 := Add(s3);
      assert s4.stack[1] == 0x240;
      var s5 := Swap(s4, 2);
      assert s5.stack[1] == 0x240;
      var s6 := Pop(s5);
      assert s6.stack[0] == 0x240;
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0140);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Dup(s10, 3);
      var s12 := PushN(s11, 2, 0x02a0);
      var s13 := Add(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 1, 0x20);
      var s17 := Dup(s16, 2);
      var s18 := Add(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := PushN(s20, 2, 0x0220);
      var s22 := MLoad(s21);
      var s23 := PushN(s22, 1, 0x20);
      var s24 := Dup(s23, 3);
      var s25 := PushN(s24, 2, 0x02a0);
      var s26 := Add(s25);
      var s27 := Add(s26);
      var s28 := MStore(s27);
      var s29 := PushN(s28, 1, 0x20);
      var s30 := Dup(s29, 2);
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s118(s31, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 121
    * Starting at 0xae0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 2, 0x02a0);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 2, 0x02a0);
      var s7 := Swap(s6, 1);
      var s8 := Pop(s7);
      var s9 := Dup(s8, 1);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Add(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x0340);
      var s15 := Dup(s14, 3);
      var s16 := Dup(s15, 5);
      var s17 := PushN(s16, 1, 0x00);
      var s18 := PushN(s17, 1, 0x04);
      var s19 := Gas(s18);
      var s20 := Call(s19);
      var s21 := IsZero(s20);
      var s22 := PushN(s21, 2, 0x17ce);
      assert s22.stack[0] == 0x17ce;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s23, gas - 1)
      else
        ExecuteFromCFGNode_s119(s23, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 122
    * Starting at 0xb02
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x0400);
      var s5 := PushN(s4, 2, 0x0340);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0360);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 1, 0x01);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 1, 0x05);
      var s13 := Dup(s12, 2);
      var s14 := Lt(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x17ce);
      assert s16.stack[0] == 0x17ce;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s17, gas - 1)
      else
        ExecuteFromCFGNode_s120(s17, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 123
    * Starting at 0xb20
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s9, gas - 1)
      else
        ExecuteFromCFGNode_s121(s9, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 124
    * Starting at 0xb2c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := ReturnDataSize(s1);
      var s3 := Dup(s2, 1);
      var s4 := Dup(s3, 3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := PushN(s6, 2, 0x0b3c);
      assert s7.stack[0] == 0xb3c;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s8, gas - 1)
      else
        ExecuteFromCFGNode_s122(s8, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 125
    * Starting at 0xb37
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 2, 0x0b3e);
      assert s2.stack[0] == 0xb3e;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s3, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 127
    * Starting at 0xb3e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := PushN(s5, 2, 0x03e0);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x03e0);
      var s9 := Dup(s8, 1);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Add(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x0160);
      var s15 := Dup(s14, 3);
      var s16 := Dup(s15, 5);
      var s17 := PushN(s16, 1, 0x00);
      var s18 := PushN(s17, 1, 0x04);
      var s19 := Gas(s18);
      var s20 := Call(s19);
      var s21 := IsZero(s20);
      var s22 := PushN(s21, 2, 0x17ce);
      assert s22.stack[0] == 0x17ce;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s23, gas - 1)
      else
        ExecuteFromCFGNode_s124(s23, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 128
    * Starting at 0xb60
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 2, 0x0160);
      var s5 := MLoad(s4);
      var s6 := Xor(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x0ba0);
      assert s8.stack[0] == 0xba0;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s128(s9, gas - 1)
      else
        ExecuteFromCFGNode_s125(s9, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 129
    * Starting at 0xb6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0160);
      var s2 := Dup(s1, 1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Dup(s6, 3);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Swap(s10, 1);
      var s12 := Sgt(s11);
      var s13 := PushN(s12, 2, 0x17ce);
      assert s13.stack[0] == 0x17ce;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s14, gas - 1)
      else
        ExecuteFromCFGNode_s126(s14, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 130
    * Starting at 0xb83
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Swap(s1, 2);
      var s3 := Swap(s2, 1);
      var s4 := Slt(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s6, gas - 1)
      else
        ExecuteFromCFGNode_s127(s6, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 131
    * Starting at 0xb8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := Sub(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := Exp(s4);
      var s6 := Dup(s5, 3);
      var s7 := Div(s6);
      var s8 := Swap(s7, 1);
      var s9 := Pop(s8);
      var s10 := Swap(s9, 1);
      var s11 := Pop(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := IsZero(s13);
      var s15 := PushN(s14, 2, 0x17ce);
      assert s15.stack[0] == 0x17ce;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s16, gas - 1)
      else
        ExecuteFromCFGNode_s128(s16, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 132
    * Starting at 0xba0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0c24);
      assert s2.stack[0] == 0xc24;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s3, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 137
    * Starting at 0xc24
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc24 as nat
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

  /** Node 130
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
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

  /** Node 131
    * Segment Id for this node is: 126
    * Starting at 0xb3c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s123(s2, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
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

  /** Node 133
    * Segment Id for this node is: 133
    * Starting at 0xba5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x64);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 2, 0x0220);
      var s5 := MLoad(s4);
      var s6 := Lt(s5);
      var s7 := PushN(s6, 2, 0x17ce);
      assert s7.stack[0] == 0x17ce;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s8, gas - 1)
      else
        ExecuteFromCFGNode_s134(s8, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 134
    * Starting at 0xbb2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 20, 0x4f01aed16d97e3ab5ab2b501154dc9bb0f1a5a2c);
      var s2 := ExtCodeSize(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x17ce);
      assert s4.stack[0] == 0x17ce;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s5, gas - 1)
      else
        ExecuteFromCFGNode_s135(s5, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 135
    * Starting at 0xbcd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbcd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x64);
      var s4 := PushN(s3, 4, 0x69328dec);
      var s5 := PushN(s4, 2, 0x0240);
      assert s5.stack[0] == 0x240;
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x01);
      var s8 := PushN(s7, 1, 0x24);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 1, 0x05);
      var s11 := Dup(s10, 2);
      var s12 := Lt(s11);
      var s13 := IsZero(s12);
      var s14 := PushN(s13, 2, 0x17ce);
      assert s14.stack[0] == 0x17ce;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s15, gas - 1)
      else
        ExecuteFromCFGNode_s136(s15, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 136
    * Starting at 0xbea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 2, 0x0260);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0220);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x0280);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0140);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x02a0);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 2, 0x025c);
      var s16 := PushN(s15, 1, 0x00);
      var s17 := PushN(s16, 20, 0x4f01aed16d97e3ab5ab2b501154dc9bb0f1a5a2c);
      var s18 := Gas(s17);
      var s19 := Call(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x17ce);
      assert s21.stack[0] == 0x17ce;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s22, gas - 1)
      else
        ExecuteFromCFGNode_s129(s22, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 108
    * Starting at 0x973
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x973 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s106(s2, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 99
    * Starting at 0x852
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x852 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 1, 0x02);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Lt(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s9, gas - 1)
      else
        ExecuteFromCFGNode_s139(s9, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 100
    * Starting at 0x85f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85f as nat
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
      var s8 := PushN(s7, 2, 0x01e0);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x00);
      var s11 := PushN(s10, 1, 0x04);
      var s12 := PushN(s11, 2, 0x0220);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 32, 0xe8eda9df00000000000000000000000000000000000000000000000000000000);
      var s15 := PushN(s14, 2, 0x0240);
      assert s15.stack[0] == 0x240;
      var s16 := MStore(s15);
      var s17 := PushN(s16, 2, 0x0220);
      var s18 := PushN(s17, 1, 0x04);
      var s19 := Dup(s18, 1);
      var s20 := PushN(s19, 1, 0x20);
      var s21 := Dup(s20, 5);
      var s22 := PushN(s21, 2, 0x0280);
      var s23 := Add(s22);
      var s24 := Add(s23);
      var s25 := Dup(s24, 3);
      var s26 := PushN(s25, 1, 0x20);
      var s27 := Dup(s26, 6);
      var s28 := Add(s27);
      var s29 := PushN(s28, 1, 0x00);
      var s30 := PushN(s29, 1, 0x04);
      var s31 := Gas(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s140(s31, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 101
    * Starting at 0x8af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Call(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Dup(s3, 1);
      var s5 := MLoad(s4);
      var s6 := Dup(s5, 3);
      var s7 := Add(s6);
      var s8 := Swap(s7, 2);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := PushN(s10, 1, 0x01);
      var s12 := PushN(s11, 1, 0x04);
      var s13 := CallDataLoad(s12);
      var s14 := PushN(s13, 1, 0x05);
      var s15 := Dup(s14, 2);
      var s16 := Lt(s15);
      var s17 := IsZero(s16);
      var s18 := PushN(s17, 2, 0x17ce);
      assert s18.stack[0] == 0x17ce;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s19, gas - 1)
      else
        ExecuteFromCFGNode_s141(s19, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 102
    * Starting at 0x8c7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := Dup(s5, 3);
      var s7 := PushN(s6, 2, 0x0280);
      var s8 := Add(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Dup(s11, 2);
      var s13 := Add(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := PushN(s15, 2, 0x01c0);
      var s17 := MLoad(s16);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 3);
      var s20 := PushN(s19, 2, 0x0280);
      var s21 := Add(s20);
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := PushN(s23, 1, 0x20);
      var s25 := Dup(s24, 2);
      var s26 := Add(s25);
      var s27 := Swap(s26, 1);
      var s28 := Pop(s27);
      var s29 := Address(s28);
      var s30 := PushN(s29, 1, 0x20);
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s142(s31, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 103
    * Starting at 0x8f2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0280);
      var s2 := Add(s1);
      var s3 := Add(s2);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := Dup(s5, 2);
      var s7 := Add(s6);
      var s8 := Swap(s7, 1);
      var s9 := Pop(s8);
      var s10 := PushN(s9, 1, 0x00);
      var s11 := SLoad(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Dup(s12, 3);
      var s14 := PushN(s13, 2, 0x0280);
      var s15 := Add(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 2);
      var s20 := Add(s19);
      var s21 := Swap(s20, 1);
      var s22 := Pop(s21);
      var s23 := Dup(s22, 1);
      var s24 := PushN(s23, 2, 0x0280);
      var s25 := MStore(s24);
      var s26 := PushN(s25, 2, 0x0280);
      var s27 := Swap(s26, 1);
      var s28 := Pop(s27);
      var s29 := Dup(s28, 1);
      var s30 := MLoad(s29);
      var s31 := PushN(s30, 1, 0x20);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s143(s31, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 104
    * Starting at 0x91e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      var s2 := Dup(s1, 1);
      var s3 := PushN(s2, 2, 0x0360);
      var s4 := Dup(s3, 3);
      var s5 := Dup(s4, 5);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := PushN(s6, 1, 0x04);
      var s8 := Gas(s7);
      var s9 := Call(s8);
      var s10 := IsZero(s9);
      var s11 := PushN(s10, 2, 0x17ce);
      assert s11.stack[0] == 0x17ce;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s12, gas - 1)
      else
        ExecuteFromCFGNode_s144(s12, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 105
    * Starting at 0x930
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x930 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 1, 0x00);
      var s5 := PushN(s4, 2, 0x0360);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0380);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 20, 0x4f01aed16d97e3ab5ab2b501154dc9bb0f1a5a2c);
      var s10 := Gas(s9);
      var s11 := Call(s10);
      var s12 := IsZero(s11);
      var s13 := PushN(s12, 2, 0x17ce);
      assert s13.stack[0] == 0x17ce;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s14, gas - 1)
      else
        ExecuteFromCFGNode_s104(s14, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 84
    * Starting at 0x738
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x738 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s90(s2, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 73
    * Starting at 0x631
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x631 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xe2ad025a);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x0657);
      assert s6.stack[0] == 0x657;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s7, gas - 1)
      else
        ExecuteFromCFGNode_s147(s7, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 74
    * Starting at 0x63e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x84);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0xa0);
      var s4 := Shr(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s148(s6, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 75
    * Starting at 0x648
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x648 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 1, 0x84);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := CallDataCopy(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x065c);
      assert s7.stack[0] == 0x65c;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s8, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 76
    * Starting at 0x657
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x657 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0c26);
      assert s2.stack[0] == 0xc26;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s3, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 138
    * Starting at 0xc26
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xe3bff5ce);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x0c3c);
      assert s6.stack[0] == 0xc3c;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s7, gas - 1)
      else
        ExecuteFromCFGNode_s151(s7, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 139
    * Starting at 0xc33
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 2, 0x0140);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x0c67);
      assert s4.stack[0] == 0xc67;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s5, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 144
    * Starting at 0xc67
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x0220);
      var s4 := PushN(s3, 1, 0x64);
      var s5 := PushN(s4, 4, 0x23b872dd);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MStore(s6);
      var s8 := Caller(s7);
      var s9 := PushN(s8, 2, 0x0180);
      var s10 := MStore(s9);
      var s11 := Address(s10);
      var s12 := PushN(s11, 2, 0x01a0);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 1, 0x04);
      var s15 := CallDataLoad(s14);
      var s16 := PushN(s15, 2, 0x01c0);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 2, 0x017c);
      var s19 := PushN(s18, 1, 0x00);
      var s20 := PushN(s19, 1, 0x0b);
      var s21 := SLoad(s20);
      var s22 := Gas(s21);
      var s23 := Call(s22);
      var s24 := IsZero(s23);
      var s25 := PushN(s24, 2, 0x17ce);
      assert s25.stack[0] == 0x17ce;
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s26, gas - 1)
      else
        ExecuteFromCFGNode_s153(s26, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 145
    * Starting at 0xc98
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s154(s6, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 146
    * Starting at 0xca1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0220);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x84);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 2, 0x0180);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 1, 0xa4);
      var s13 := CallDataLoad(s12);
      var s14 := PushN(s13, 2, 0x01a0);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 1, 0x09);
      var s17 := SLoad(s16);
      var s18 := ExtCodeSize(s17);
      var s19 := IsZero(s18);
      var s20 := PushN(s19, 2, 0x17ce);
      assert s20.stack[0] == 0x17ce;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s21, gas - 1)
      else
        ExecuteFromCFGNode_s155(s21, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 147
    * Starting at 0xcc5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x84);
      var s4 := PushN(s3, 4, 0xecb586a5);
      var s5 := PushN(s4, 2, 0x01c0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x04);
      var s8 := CallDataLoad(s7);
      var s9 := PushN(s8, 2, 0x01e0);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0160);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x0200);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 2, 0x0180);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 2, 0x0220);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 2, 0x01a0);
      var s20 := MLoad(s19);
      var s21 := PushN(s20, 2, 0x0240);
      assert s21.stack[0] == 0x240;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 2, 0x01dc);
      var s24 := PushN(s23, 1, 0x00);
      var s25 := PushN(s24, 1, 0x09);
      var s26 := SLoad(s25);
      var s27 := Gas(s26);
      var s28 := Call(s27);
      var s29 := IsZero(s28);
      var s30 := PushN(s29, 2, 0x17ce);
      assert s30.stack[0] == 0x17ce;
      var s31 := JumpI(s30);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s30.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s31, gas - 1)
      else
        ExecuteFromCFGNode_s156(s31, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 148
    * Starting at 0xd02
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 2, 0x0260);
      var s3 := PushN(s2, 1, 0x24);
      var s4 := PushN(s3, 4, 0x70a08231);
      var s5 := PushN(s4, 2, 0x01e0);
      var s6 := MStore(s5);
      var s7 := Address(s6);
      var s8 := PushN(s7, 2, 0x0200);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x01fc);
      var s11 := PushN(s10, 1, 0x01);
      var s12 := SLoad(s11);
      var s13 := Gas(s12);
      var s14 := StaticCall(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x17ce);
      assert s16.stack[0] == 0x17ce;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s17, gas - 1)
      else
        ExecuteFromCFGNode_s157(s17, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 149
    * Starting at 0xd24
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s158(s6, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 150
    * Starting at 0xd2d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0260);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x01c0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x24);
      var s8 := CallDataLoad(s7);
      var s9 := PushN(s8, 2, 0x01e0);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x44);
      var s12 := CallDataLoad(s11);
      var s13 := PushN(s12, 2, 0x0200);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 1, 0x64);
      var s16 := CallDataLoad(s15);
      var s17 := PushN(s16, 2, 0x0220);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 1, 0x60);
      var s20 := PushN(s19, 2, 0x03a0);
      var s21 := PushN(s20, 1, 0xa4);
      var s22 := PushN(s21, 4, 0xfce64736);
      var s23 := PushN(s22, 2, 0x02a0);
      var s24 := MStore(s23);
      var s25 := PushN(s24, 2, 0x01c0);
      var s26 := MLoad(s25);
      var s27 := PushN(s26, 2, 0x02c0);
      var s28 := MStore(s27);
      var s29 := PushN(s28, 2, 0x01e0);
      var s30 := MLoad(s29);
      var s31 := PushN(s30, 2, 0x02e0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s159(s31, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 151
    * Starting at 0xd6c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      var s2 := PushN(s1, 2, 0x0200);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0300);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 2, 0x0220);
      var s7 := MLoad(s6);
      var s8 := PushN(s7, 2, 0x0320);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x01);
      var s11 := PushN(s10, 2, 0x0340);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 2, 0x02bc);
      var s14 := PushN(s13, 1, 0x00);
      var s15 := PushN(s14, 1, 0x0a);
      var s16 := SLoad(s15);
      var s17 := Gas(s16);
      var s18 := Call(s17);
      var s19 := IsZero(s18);
      var s20 := PushN(s19, 2, 0x17ce);
      assert s20.stack[0] == 0x17ce;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s21, gas - 1)
      else
        ExecuteFromCFGNode_s160(s21, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 152
    * Starting at 0xd92
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x5f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s161(s6, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 153
    * Starting at 0xd9b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x03a0);
      var s4 := Dup(s3, 1);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 2, 0x0240);
      assert s6.stack[0] == 0x240;
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := PushN(s8, 1, 0x20);
      var s10 := Add(s9);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 2, 0x0260);
      var s13 := MStore(s12);
      var s14 := Dup(s13, 1);
      var s15 := PushN(s14, 1, 0x40);
      var s16 := Add(s15);
      var s17 := MLoad(s16);
      var s18 := PushN(s17, 2, 0x0280);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := PushN(s20, 2, 0x02a0);
      var s22 := PushN(s21, 1, 0x00);
      var s23 := PushN(s22, 1, 0x03);
      var s24 := Dup(s23, 2);
      var s25 := Dup(s24, 4);
      var s26 := MStore(s25);
      var s27 := Add(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s162(s27, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 154
    * Starting at 0xdc5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := PushN(s3, 2, 0x0320);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 32, 0xa9059cbb00000000000000000000000000000000000000000000000000000000);
      var s7 := PushN(s6, 2, 0x0340);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0320);
      var s10 := PushN(s9, 1, 0x04);
      var s11 := Dup(s10, 1);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Dup(s12, 5);
      var s14 := PushN(s13, 2, 0x0380);
      var s15 := Add(s14);
      var s16 := Add(s15);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 6);
      var s20 := Add(s19);
      var s21 := PushN(s20, 1, 0x00);
      var s22 := PushN(s21, 1, 0x04);
      var s23 := Gas(s22);
      var s24 := Call(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Dup(s26, 1);
      var s28 := MLoad(s27);
      var s29 := Dup(s28, 3);
      var s30 := Add(s29);
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s163(s31, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 155
    * Starting at 0xe13
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := Dup(s5, 3);
      var s7 := PushN(s6, 2, 0x0380);
      var s8 := Add(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Dup(s11, 2);
      var s13 := Add(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := PushN(s15, 2, 0x0240);
      assert s16.stack[0] == 0x240;
      var s17 := PushN(s16, 2, 0x02a0);
      assert s17.stack[1] == 0x240;
      var s18 := MLoad(s17);
      assert s18.stack[1] == 0x240;
      var s19 := PushN(s18, 1, 0x03);
      assert s19.stack[2] == 0x240;
      var s20 := Dup(s19, 2);
      assert s20.stack[3] == 0x240;
      var s21 := Lt(s20);
      assert s21.stack[2] == 0x240;
      var s22 := IsZero(s21);
      assert s22.stack[2] == 0x240;
      var s23 := PushN(s22, 2, 0x17ce);
      assert s23.stack[0] == 0x17ce;
      assert s23.stack[3] == 0x240;
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s190(s24, gas - 1)
      else
        ExecuteFromCFGNode_s164(s24, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 156
    * Starting at 0xe38
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe38 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[2] == 0x240;
      var s2 := Mul(s1);
      assert s2.stack[1] == 0x240;
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := Dup(s5, 3);
      var s7 := PushN(s6, 2, 0x0380);
      var s8 := Add(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Dup(s11, 2);
      var s13 := Add(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := Dup(s15, 1);
      var s17 := PushN(s16, 2, 0x0380);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 2, 0x0380);
      var s20 := Swap(s19, 1);
      var s21 := Pop(s20);
      var s22 := Dup(s21, 1);
      var s23 := MLoad(s22);
      var s24 := PushN(s23, 1, 0x20);
      var s25 := Add(s24);
      var s26 := Dup(s25, 1);
      var s27 := PushN(s26, 2, 0x0420);
      var s28 := Dup(s27, 3);
      var s29 := Dup(s28, 5);
      var s30 := PushN(s29, 1, 0x00);
      var s31 := PushN(s30, 1, 0x04);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s165(s31, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 157
    * Starting at 0xe65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Gas(s0);
      var s2 := Call(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x17ce);
      assert s4.stack[0] == 0x17ce;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s5, gas - 1)
      else
        ExecuteFromCFGNode_s166(s5, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 158
    * Starting at 0xe6c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x04e0);
      var s5 := PushN(s4, 2, 0x0420);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0440);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 1, 0x01);
      var s10 := PushN(s9, 2, 0x02a0);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 1, 0x05);
      var s13 := Dup(s12, 2);
      var s14 := Lt(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x17ce);
      assert s16.stack[0] == 0x17ce;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s17, gas - 1)
      else
        ExecuteFromCFGNode_s167(s17, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 159
    * Starting at 0xe8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s9, gas - 1)
      else
        ExecuteFromCFGNode_s168(s9, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 160
    * Starting at 0xe97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := ReturnDataSize(s1);
      var s3 := Dup(s2, 1);
      var s4 := Dup(s3, 3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := PushN(s6, 2, 0x0ea7);
      assert s7.stack[0] == 0xea7;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s8, gas - 1)
      else
        ExecuteFromCFGNode_s169(s8, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 161
    * Starting at 0xea2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 2, 0x0ea9);
      assert s2.stack[0] == 0xea9;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s3, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 163
    * Starting at 0xea9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := PushN(s5, 2, 0x04c0);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x04c0);
      var s9 := Dup(s8, 1);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Add(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x02c0);
      var s15 := Dup(s14, 3);
      var s16 := Dup(s15, 5);
      var s17 := PushN(s16, 1, 0x00);
      var s18 := PushN(s17, 1, 0x04);
      var s19 := Gas(s18);
      var s20 := Call(s19);
      var s21 := IsZero(s20);
      var s22 := PushN(s21, 2, 0x17ce);
      assert s22.stack[0] == 0x17ce;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s23, gas - 1)
      else
        ExecuteFromCFGNode_s171(s23, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 164
    * Starting at 0xecb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 2, 0x02c0);
      var s5 := MLoad(s4);
      var s6 := Xor(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x0f0b);
      assert s8.stack[0] == 0xf0b;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s9, gas - 1)
      else
        ExecuteFromCFGNode_s172(s9, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 165
    * Starting at 0xed9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x02c0);
      var s2 := Dup(s1, 1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Dup(s6, 3);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Swap(s10, 1);
      var s12 := Sgt(s11);
      var s13 := PushN(s12, 2, 0x17ce);
      assert s13.stack[0] == 0x17ce;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s14, gas - 1)
      else
        ExecuteFromCFGNode_s173(s14, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 166
    * Starting at 0xeee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Swap(s1, 2);
      var s3 := Swap(s2, 1);
      var s4 := Slt(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s6, gas - 1)
      else
        ExecuteFromCFGNode_s174(s6, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 167
    * Starting at 0xef6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := Sub(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := Exp(s4);
      var s6 := Dup(s5, 3);
      var s7 := Div(s6);
      var s8 := Swap(s7, 1);
      var s9 := Pop(s8);
      var s10 := Swap(s9, 1);
      var s11 := Pop(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := IsZero(s13);
      var s15 := PushN(s14, 2, 0x17ce);
      assert s15.stack[0] == 0x17ce;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s16, gas - 1)
      else
        ExecuteFromCFGNode_s175(s16, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 168
    * Starting at 0xf0b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s176(s1, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 169
    * Starting at 0xf0c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0c as nat
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
      var s12 := PushN(s11, 2, 0x0dc5);
      assert s12.stack[0] == 0xdc5;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s162(s13, gas - 1)
      else
        ExecuteFromCFGNode_s177(s13, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 170
    * Starting at 0xf1c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := PushN(s3, 2, 0x02a0);
      var s5 := PushN(s4, 1, 0x03);
      var s6 := PushN(s5, 1, 0x02);
      var s7 := Dup(s6, 2);
      var s8 := Dup(s7, 4);
      var s9 := MStore(s8);
      var s10 := Add(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s178(s10, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 171
    * Starting at 0xf2a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x0340);
      var s4 := PushN(s3, 1, 0x24);
      var s5 := PushN(s4, 4, 0x70a08231);
      var s6 := PushN(s5, 2, 0x02c0);
      var s7 := MStore(s6);
      var s8 := Address(s7);
      var s9 := PushN(s8, 2, 0x02e0);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x02dc);
      var s12 := PushN(s11, 1, 0x01);
      var s13 := PushN(s12, 2, 0x02a0);
      var s14 := MLoad(s13);
      var s15 := PushN(s14, 1, 0x02);
      var s16 := Dup(s15, 1);
      var s17 := Dup(s16, 3);
      var s18 := Lt(s17);
      var s19 := PushN(s18, 2, 0x17ce);
      assert s19.stack[0] == 0x17ce;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s20, gas - 1)
      else
        ExecuteFromCFGNode_s179(s20, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 172
    * Starting at 0xf52
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

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
      var s12 := PushN(s11, 2, 0x17ce);
      assert s12.stack[0] == 0x17ce;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s187(s13, gas - 1)
      else
        ExecuteFromCFGNode_s180(s13, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 173
    * Starting at 0xf62
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x01);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := StaticCall(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s9, gas - 1)
      else
        ExecuteFromCFGNode_s181(s9, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 174
    * Starting at 0xf6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s6, gas - 1)
      else
        ExecuteFromCFGNode_s182(s6, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 175
    * Starting at 0xf77
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0340);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x01c0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 20, 0x4f01aed16d97e3ab5ab2b501154dc9bb0f1a5a2c);
      var s8 := ExtCodeSize(s7);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x17ce);
      assert s10.stack[0] == 0x17ce;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s11, gas - 1)
      else
        ExecuteFromCFGNode_s183(s11, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 176
    * Starting at 0xf9d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x64);
      var s4 := PushN(s3, 4, 0x69328dec);
      var s5 := PushN(s4, 2, 0x02c0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x01);
      var s8 := PushN(s7, 2, 0x02a0);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x05);
      var s11 := Dup(s10, 2);
      var s12 := Lt(s11);
      var s13 := IsZero(s12);
      var s14 := PushN(s13, 2, 0x17ce);
      assert s14.stack[0] == 0x17ce;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s15, gas - 1)
      else
        ExecuteFromCFGNode_s184(s15, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 177
    * Starting at 0xfbb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 2, 0x02e0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x01c0);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x0300);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0140);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x0320);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 2, 0x02dc);
      var s16 := PushN(s15, 1, 0x00);
      var s17 := PushN(s16, 20, 0x4f01aed16d97e3ab5ab2b501154dc9bb0f1a5a2c);
      var s18 := Gas(s17);
      var s19 := Call(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x17ce);
      assert s21.stack[0] == 0x17ce;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s22, gas - 1)
      else
        ExecuteFromCFGNode_s185(s22, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 178
    * Starting at 0xff5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff5 as nat
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
      var s12 := PushN(s11, 2, 0x0f2a);
      assert s12.stack[0] == 0xf2a;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s13, gas - 1)
      else
        ExecuteFromCFGNode_s186(s13, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 179
    * Starting at 0x1005
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1005 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Stop(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 187
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
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

  /** Node 188
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
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

  /** Node 189
    * Segment Id for this node is: 162
    * Starting at 0xea7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s170(s2, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 285
    * Starting at 0x17ce
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x240

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x240;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[2] == 0x240;
      var s3 := Dup(s2, 1);
      assert s3.stack[3] == 0x240;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 191
    * Segment Id for this node is: 140
    * Starting at 0xc3c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x4f626a31);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x0c62);
      assert s6.stack[0] == 0xc62;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s7, gas - 1)
      else
        ExecuteFromCFGNode_s192(s7, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 141
    * Starting at 0xc49
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xc4);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0xa0);
      var s4 := Shr(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s193(s6, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 142
    * Starting at 0xc53
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc53 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 1, 0xc4);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := CallDataCopy(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0c67);
      assert s7.stack[0] == 0xc67;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s8, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 143
    * Starting at 0xc62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x1009);
      assert s2.stack[0] == 0x1009;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s3, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 180
    * Starting at 0x1009
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1009 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xf1dc3cc9);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x101f);
      assert s6.stack[0] == 0x101f;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s7, gas - 1)
      else
        ExecuteFromCFGNode_s196(s7, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 181
    * Starting at 0x1016
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1016 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 2, 0x0140);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x104a);
      assert s4.stack[0] == 0x104a;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s5, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 186
    * Starting at 0x104a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x0220);
      var s4 := PushN(s3, 1, 0x64);
      var s5 := PushN(s4, 4, 0x23b872dd);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MStore(s6);
      var s8 := Caller(s7);
      var s9 := PushN(s8, 2, 0x0180);
      var s10 := MStore(s9);
      var s11 := Address(s10);
      var s12 := PushN(s11, 2, 0x01a0);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 1, 0x04);
      var s15 := CallDataLoad(s14);
      var s16 := PushN(s15, 2, 0x01c0);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 2, 0x017c);
      var s19 := PushN(s18, 1, 0x00);
      var s20 := PushN(s19, 1, 0x0b);
      var s21 := SLoad(s20);
      var s22 := Gas(s21);
      var s23 := Call(s22);
      var s24 := IsZero(s23);
      var s25 := PushN(s24, 2, 0x17ce);
      assert s25.stack[0] == 0x17ce;
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s26, gas - 1)
      else
        ExecuteFromCFGNode_s198(s26, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 187
    * Starting at 0x107b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s199(s6, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 188
    * Starting at 0x1084
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1084 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0220);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x03);
      var s9 := PushN(s8, 1, 0x24);
      var s10 := CallDataLoad(s9);
      var s11 := Lt(s10);
      var s12 := PushN(s11, 2, 0x10b2);
      assert s12.stack[0] == 0x10b2;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s13, gas - 1)
      else
        ExecuteFromCFGNode_s200(s13, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 189
    * Starting at 0x109b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109b as nat
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
      var s7 := PushN(s6, 2, 0x17ce);
      assert s7.stack[0] == 0x17ce;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s8, gas - 1)
      else
        ExecuteFromCFGNode_s201(s8, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 190
    * Starting at 0x10a7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a7 as nat
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
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s202(s9, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 191
    * Starting at 0x10b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x09);
      var s3 := SLoad(s2);
      var s4 := ExtCodeSize(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x17ce);
      assert s6.stack[0] == 0x17ce;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s7, gas - 1)
      else
        ExecuteFromCFGNode_s203(s7, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 192
    * Starting at 0x10bc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x64);
      var s4 := PushN(s3, 4, 0xf1dc3cc9);
      var s5 := PushN(s4, 2, 0x0180);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x04);
      var s8 := CallDataLoad(s7);
      var s9 := PushN(s8, 2, 0x01a0);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0160);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x01c0);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 1, 0x00);
      var s16 := PushN(s15, 2, 0x01e0);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 2, 0x019c);
      var s19 := PushN(s18, 1, 0x00);
      var s20 := PushN(s19, 1, 0x09);
      var s21 := SLoad(s20);
      var s22 := Gas(s21);
      var s23 := Call(s22);
      var s24 := IsZero(s23);
      var s25 := PushN(s24, 2, 0x17ce);
      assert s25.stack[0] == 0x17ce;
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s26, gas - 1)
      else
        ExecuteFromCFGNode_s204(s26, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 193
    * Starting at 0x10ef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 2, 0x0220);
      var s3 := PushN(s2, 1, 0x24);
      var s4 := PushN(s3, 4, 0x70a08231);
      var s5 := PushN(s4, 2, 0x01a0);
      var s6 := MStore(s5);
      var s7 := Address(s6);
      var s8 := PushN(s7, 2, 0x01c0);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x01bc);
      var s11 := PushN(s10, 1, 0x01);
      var s12 := PushN(s11, 2, 0x0160);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 1, 0x03);
      var s15 := Dup(s14, 2);
      var s16 := Lt(s15);
      var s17 := IsZero(s16);
      var s18 := PushN(s17, 2, 0x17ce);
      assert s18.stack[0] == 0x17ce;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s19, gas - 1)
      else
        ExecuteFromCFGNode_s205(s19, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 194
    * Starting at 0x1116
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1116 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x01);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := StaticCall(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s9, gas - 1)
      else
        ExecuteFromCFGNode_s206(s9, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 195
    * Starting at 0x1122
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1122 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s207(s6, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 196
    * Starting at 0x112b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0220);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0180);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0160);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x12ce);
      assert s9.stack[0] == 0x12ce;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s226(s10, gas - 1)
      else
        ExecuteFromCFGNode_s208(s10, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 197
    * Starting at 0x113e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 2, 0x0280);
      var s3 := PushN(s2, 1, 0x84);
      var s4 := PushN(s3, 4, 0x517a55a3);
      var s5 := PushN(s4, 2, 0x01a0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0180);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x01c0);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x24);
      var s12 := CallDataLoad(s11);
      var s13 := PushN(s12, 1, 0x40);
      var s14 := MLoad(s13);
      var s15 := Dup(s14, 2);
      var s16 := Gt(s15);
      var s17 := PushN(s16, 2, 0x17ce);
      assert s17.stack[0] == 0x17ce;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s18, gas - 1)
      else
        ExecuteFromCFGNode_s209(s18, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 198
    * Starting at 0x1162
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1162 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01e0);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x44);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 2, 0x0200);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x01);
      var s8 := PushN(s7, 2, 0x0220);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x01bc);
      var s11 := PushN(s10, 1, 0x00);
      var s12 := PushN(s11, 1, 0x0a);
      var s13 := SLoad(s12);
      var s14 := Gas(s13);
      var s15 := Call(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x17ce);
      assert s17.stack[0] == 0x17ce;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s18, gas - 1)
      else
        ExecuteFromCFGNode_s210(s18, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 199
    * Starting at 0x1182
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1182 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s211(s6, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 200
    * Starting at 0x118b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0280);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0180);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 1, 0x04);
      var s9 := PushN(s8, 2, 0x0200);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 32, 0xa9059cbb00000000000000000000000000000000000000000000000000000000);
      var s12 := PushN(s11, 2, 0x0220);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 2, 0x0200);
      var s15 := PushN(s14, 1, 0x04);
      var s16 := Dup(s15, 1);
      var s17 := PushN(s16, 1, 0x20);
      var s18 := Dup(s17, 5);
      var s19 := PushN(s18, 2, 0x0260);
      var s20 := Add(s19);
      var s21 := Add(s20);
      var s22 := Dup(s21, 3);
      var s23 := PushN(s22, 1, 0x20);
      var s24 := Dup(s23, 6);
      var s25 := Add(s24);
      var s26 := PushN(s25, 1, 0x00);
      var s27 := PushN(s26, 1, 0x04);
      var s28 := Gas(s27);
      var s29 := Call(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s212(s31, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 201
    * Starting at 0x11de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := MLoad(s1);
      var s3 := Dup(s2, 3);
      var s4 := Add(s3);
      var s5 := Swap(s4, 2);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0140);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Dup(s10, 3);
      var s12 := PushN(s11, 2, 0x0260);
      var s13 := Add(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 1, 0x20);
      var s17 := Dup(s16, 2);
      var s18 := Add(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := PushN(s20, 2, 0x0180);
      var s22 := MLoad(s21);
      var s23 := PushN(s22, 1, 0x20);
      var s24 := Dup(s23, 3);
      var s25 := PushN(s24, 2, 0x0260);
      var s26 := Add(s25);
      var s27 := Add(s26);
      var s28 := MStore(s27);
      var s29 := PushN(s28, 1, 0x20);
      var s30 := Dup(s29, 2);
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s213(s31, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 202
    * Starting at 0x1209
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1209 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 2, 0x0260);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 2, 0x0260);
      var s7 := Swap(s6, 1);
      var s8 := Pop(s7);
      var s9 := Dup(s8, 1);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Add(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x0300);
      var s15 := Dup(s14, 3);
      var s16 := Dup(s15, 5);
      var s17 := PushN(s16, 1, 0x00);
      var s18 := PushN(s17, 1, 0x04);
      var s19 := Gas(s18);
      var s20 := Call(s19);
      var s21 := IsZero(s20);
      var s22 := PushN(s21, 2, 0x17ce);
      assert s22.stack[0] == 0x17ce;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s23, gas - 1)
      else
        ExecuteFromCFGNode_s214(s23, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 203
    * Starting at 0x122b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x03c0);
      var s5 := PushN(s4, 2, 0x0300);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0320);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 1, 0x01);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 1, 0x05);
      var s13 := Dup(s12, 2);
      var s14 := Lt(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x17ce);
      assert s16.stack[0] == 0x17ce;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s17, gas - 1)
      else
        ExecuteFromCFGNode_s215(s17, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 204
    * Starting at 0x1249
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1249 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s9, gas - 1)
      else
        ExecuteFromCFGNode_s216(s9, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 205
    * Starting at 0x1255
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1255 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := ReturnDataSize(s1);
      var s3 := Dup(s2, 1);
      var s4 := Dup(s3, 3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := PushN(s6, 2, 0x1265);
      assert s7.stack[0] == 0x1265;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s225(s8, gas - 1)
      else
        ExecuteFromCFGNode_s217(s8, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 206
    * Starting at 0x1260
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1260 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 2, 0x1267);
      assert s2.stack[0] == 0x1267;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s3, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 208
    * Starting at 0x1267
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1267 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := PushN(s5, 2, 0x03a0);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x03a0);
      var s9 := Dup(s8, 1);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Add(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x01a0);
      var s15 := Dup(s14, 3);
      var s16 := Dup(s15, 5);
      var s17 := PushN(s16, 1, 0x00);
      var s18 := PushN(s17, 1, 0x04);
      var s19 := Gas(s18);
      var s20 := Call(s19);
      var s21 := IsZero(s20);
      var s22 := PushN(s21, 2, 0x17ce);
      assert s22.stack[0] == 0x17ce;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s23, gas - 1)
      else
        ExecuteFromCFGNode_s219(s23, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 209
    * Starting at 0x1289
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1289 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 2, 0x01a0);
      var s5 := MLoad(s4);
      var s6 := Xor(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x12c9);
      assert s8.stack[0] == 0x12c9;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s223(s9, gas - 1)
      else
        ExecuteFromCFGNode_s220(s9, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 210
    * Starting at 0x1297
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1297 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01a0);
      var s2 := Dup(s1, 1);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Dup(s6, 3);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Swap(s10, 1);
      var s12 := Sgt(s11);
      var s13 := PushN(s12, 2, 0x17ce);
      assert s13.stack[0] == 0x17ce;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s14, gas - 1)
      else
        ExecuteFromCFGNode_s221(s14, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 211
    * Starting at 0x12ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Swap(s1, 2);
      var s3 := Swap(s2, 1);
      var s4 := Slt(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s6, gas - 1)
      else
        ExecuteFromCFGNode_s222(s6, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 212
    * Starting at 0x12b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := Sub(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := Exp(s4);
      var s6 := Dup(s5, 3);
      var s7 := Div(s6);
      var s8 := Swap(s7, 1);
      var s9 := Pop(s8);
      var s10 := Swap(s9, 1);
      var s11 := Pop(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := IsZero(s13);
      var s15 := PushN(s14, 2, 0x17ce);
      assert s15.stack[0] == 0x17ce;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s16, gas - 1)
      else
        ExecuteFromCFGNode_s223(s16, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 213
    * Starting at 0x12c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x134d);
      assert s2.stack[0] == 0x134d;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s3, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 218
    * Starting at 0x134d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x134d as nat
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

  /** Node 225
    * Segment Id for this node is: 207
    * Starting at 0x1265
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1265 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s218(s2, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 214
    * Starting at 0x12ce
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x44);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 2, 0x0180);
      var s5 := MLoad(s4);
      var s6 := Lt(s5);
      var s7 := PushN(s6, 2, 0x17ce);
      assert s7.stack[0] == 0x17ce;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s8, gas - 1)
      else
        ExecuteFromCFGNode_s227(s8, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 215
    * Starting at 0x12db
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 20, 0x4f01aed16d97e3ab5ab2b501154dc9bb0f1a5a2c);
      var s2 := ExtCodeSize(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x17ce);
      assert s4.stack[0] == 0x17ce;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s5, gas - 1)
      else
        ExecuteFromCFGNode_s228(s5, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 216
    * Starting at 0x12f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x64);
      var s4 := PushN(s3, 4, 0x69328dec);
      var s5 := PushN(s4, 2, 0x01a0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x01);
      var s8 := PushN(s7, 1, 0x24);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 1, 0x05);
      var s11 := Dup(s10, 2);
      var s12 := Lt(s11);
      var s13 := IsZero(s12);
      var s14 := PushN(s13, 2, 0x17ce);
      assert s14.stack[0] == 0x17ce;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s15, gas - 1)
      else
        ExecuteFromCFGNode_s229(s15, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 217
    * Starting at 0x1313
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1313 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 2, 0x01c0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0180);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x01e0);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0140);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x0200);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 2, 0x01bc);
      var s16 := PushN(s15, 1, 0x00);
      var s17 := PushN(s16, 20, 0x4f01aed16d97e3ab5ab2b501154dc9bb0f1a5a2c);
      var s18 := Gas(s17);
      var s19 := Call(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x17ce);
      assert s21.stack[0] == 0x17ce;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s22, gas - 1)
      else
        ExecuteFromCFGNode_s224(s22, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 182
    * Starting at 0x101f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x0fbcee6e);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1045);
      assert s6.stack[0] == 0x1045;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s233(s7, gas - 1)
      else
        ExecuteFromCFGNode_s231(s7, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 183
    * Starting at 0x102c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x64);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0xa0);
      var s4 := Shr(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s232(s6, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 184
    * Starting at 0x1036
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1036 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 1, 0x64);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := CallDataCopy(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x104a);
      assert s7.stack[0] == 0x104a;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s8, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 185
    * Starting at 0x1045
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1045 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x134f);
      assert s2.stack[0] == 0x134f;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s3, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 219
    * Starting at 0x134f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x134f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x85f11d1e);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1552);
      assert s6.stack[0] == 0x1552;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s7, gas - 1)
      else
        ExecuteFromCFGNode_s235(s7, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 220
    * Starting at 0x135c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135c as nat
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
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1371);
      assert s10.stack[0] == 0x1371;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s262(s11, gas - 1)
      else
        ExecuteFromCFGNode_s236(s11, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 221
    * Starting at 0x136c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x136c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 2, 0x1373);
      assert s2.stack[0] == 0x1373;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s3, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 223
    * Starting at 0x1373
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1373 as nat
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
      var s8 := PushN(s7, 2, 0x13da);
      assert s8.stack[0] == 0x13da;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s243(s9, gas - 1)
      else
        ExecuteFromCFGNode_s238(s9, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 224
    * Starting at 0x137e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x137e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 2, 0x0200);
      var s3 := PushN(s2, 1, 0x64);
      var s4 := PushN(s3, 4, 0x5e0d443f);
      var s5 := PushN(s4, 2, 0x0140);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x04);
      var s8 := CallDataLoad(s7);
      var s9 := PushN(s8, 1, 0x40);
      var s10 := MLoad(s9);
      var s11 := Dup(s10, 2);
      var s12 := Gt(s11);
      var s13 := PushN(s12, 2, 0x17ce);
      assert s13.stack[0] == 0x17ce;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s14, gas - 1)
      else
        ExecuteFromCFGNode_s239(s14, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 225
    * Starting at 0x139a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0160);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 1, 0x24);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 1, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 2);
      var s8 := Gt(s7);
      var s9 := PushN(s8, 2, 0x17ce);
      assert s9.stack[0] == 0x17ce;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s10, gas - 1)
      else
        ExecuteFromCFGNode_s240(s10, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 226
    * Starting at 0x13aa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s7 := PushN(s6, 2, 0x015c);
      var s8 := PushN(s7, 1, 0x0a);
      var s9 := SLoad(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      var s12 := IsZero(s11);
      var s13 := PushN(s12, 2, 0x17ce);
      assert s13.stack[0] == 0x17ce;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s14, gas - 1)
      else
        ExecuteFromCFGNode_s241(s14, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 227
    * Starting at 0x13c2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s242(s6, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 228
    * Starting at 0x13cb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0200);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := Return(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 243
    * Segment Id for this node is: 229
    * Starting at 0x13da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13da as nat
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
      var s14 := PushN(s13, 2, 0x140a);
      assert s14.stack[0] == 0x140a;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s246(s15, gas - 1)
      else
        ExecuteFromCFGNode_s244(s15, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 230
    * Starting at 0x13f3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f3 as nat
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
      var s7 := PushN(s6, 2, 0x17ce);
      assert s7.stack[0] == 0x17ce;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s8, gas - 1)
      else
        ExecuteFromCFGNode_s245(s8, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 231
    * Starting at 0x13ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ff as nat
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
      ExecuteFromCFGNode_s246(s9, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 232
    * Starting at 0x140a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
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
      var s6 := IsZero(s5);
      var s7 := PushN(s6, 2, 0x1488);
      assert s7.stack[0] == 0x1488;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s260(s8, gas - 1)
      else
        ExecuteFromCFGNode_s247(s8, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 233
    * Starting at 0x1416
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1416 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x60);
      var s2 := CallDataSize(s1);
      var s3 := PushN(s2, 2, 0x01a0);
      var s4 := CallDataCopy(s3);
      var s5 := PushN(s4, 2, 0x0140);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x01a0);
      var s8 := PushN(s7, 1, 0x04);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 1, 0x03);
      var s11 := Dup(s10, 2);
      var s12 := Lt(s11);
      var s13 := IsZero(s12);
      var s14 := PushN(s13, 2, 0x17ce);
      assert s14.stack[0] == 0x17ce;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s15, gas - 1)
      else
        ExecuteFromCFGNode_s248(s15, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 234
    * Starting at 0x1430
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1430 as nat
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
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x02e0);
      var s7 := PushN(s6, 1, 0x84);
      var s8 := PushN(s7, 4, 0x3883e119);
      var s9 := PushN(s8, 2, 0x0200);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x01a0);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x0220);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 2, 0x01c0);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 2, 0x0240);
      assert s17.stack[0] == 0x240;
      var s18 := MStore(s17);
      var s19 := PushN(s18, 2, 0x01e0);
      var s20 := MLoad(s19);
      var s21 := PushN(s20, 2, 0x0260);
      var s22 := MStore(s21);
      var s23 := PushN(s22, 1, 0x01);
      var s24 := PushN(s23, 2, 0x0280);
      var s25 := MStore(s24);
      var s26 := PushN(s25, 2, 0x021c);
      var s27 := PushN(s26, 1, 0x0a);
      var s28 := SLoad(s27);
      var s29 := Gas(s28);
      var s30 := StaticCall(s29);
      var s31 := IsZero(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s249(s31, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 235
    * Starting at 0x146c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x17ce);
      assert s1.stack[0] == 0x17ce;
      var s2 := JumpI(s1);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s1.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s2, gas - 1)
      else
        ExecuteFromCFGNode_s250(s2, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 236
    * Starting at 0x1470
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1470 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s251(s6, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 237
    * Starting at 0x1479
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1479 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x02e0);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0140);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x14a0);
      assert s7.stack[0] == 0x14a0;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s8, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 240
    * Starting at 0x14a0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x0280);
      var s4 := PushN(s3, 1, 0x64);
      var s5 := PushN(s4, 4, 0x556d6e9f);
      var s6 := PushN(s5, 2, 0x01c0);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x0160);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x01e0);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x0180);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 2, 0x0200);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 2, 0x0140);
      var s17 := MLoad(s16);
      var s18 := PushN(s17, 2, 0x0220);
      var s19 := MStore(s18);
      var s20 := PushN(s19, 2, 0x01dc);
      var s21 := PushN(s20, 1, 0x09);
      var s22 := SLoad(s21);
      var s23 := Gas(s22);
      var s24 := StaticCall(s23);
      var s25 := IsZero(s24);
      var s26 := PushN(s25, 2, 0x17ce);
      assert s26.stack[0] == 0x17ce;
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s27, gas - 1)
      else
        ExecuteFromCFGNode_s253(s27, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 241
    * Starting at 0x14d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s254(s6, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 242
    * Starting at 0x14df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0280);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x01a0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0180);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x1543);
      assert s9.stack[0] == 0x1543;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s259(s10, gas - 1)
      else
        ExecuteFromCFGNode_s255(s10, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 243
    * Starting at 0x14f2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 2, 0x0260);
      var s3 := PushN(s2, 1, 0x44);
      var s4 := PushN(s3, 4, 0xcc2b27d7);
      var s5 := PushN(s4, 2, 0x01c0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x01a0);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x01e0);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x24);
      var s12 := CallDataLoad(s11);
      var s13 := PushN(s12, 1, 0x40);
      var s14 := MLoad(s13);
      var s15 := Dup(s14, 2);
      var s16 := Gt(s15);
      var s17 := PushN(s16, 2, 0x17ce);
      assert s17.stack[0] == 0x17ce;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s18, gas - 1)
      else
        ExecuteFromCFGNode_s256(s18, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 244
    * Starting at 0x1516
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1516 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0200);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 2, 0x01dc);
      var s4 := PushN(s3, 1, 0x0a);
      var s5 := SLoad(s4);
      var s6 := Gas(s5);
      var s7 := StaticCall(s6);
      var s8 := IsZero(s7);
      var s9 := PushN(s8, 2, 0x17ce);
      assert s9.stack[0] == 0x17ce;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s10, gas - 1)
      else
        ExecuteFromCFGNode_s257(s10, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 245
    * Starting at 0x1527
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1527 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s258(s6, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 246
    * Starting at 0x1530
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1530 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0260);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := Return(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 259
    * Segment Id for this node is: 248
    * Starting at 0x1543
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1543 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x01a0);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x00);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x20);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 260
    * Segment Id for this node is: 238
    * Starting at 0x1488
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1488 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 1, 0x02);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Lt(s6);
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s9, gas - 1)
      else
        ExecuteFromCFGNode_s261(s9, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 239
    * Starting at 0x1495
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1495 as nat
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
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s252(s9, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 222
    * Starting at 0x1371
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s237(s2, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 250
    * Starting at 0x1552
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1552 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x7ede89c5);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1638);
      assert s6.stack[0] == 0x1638;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s272(s7, gas - 1)
      else
        ExecuteFromCFGNode_s264(s7, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 251
    * Starting at 0x155f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x155f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xa4);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0x01);
      var s4 := Shr(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s265(s6, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 252
    * Starting at 0x1569
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1569 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x24);
      var s6 := CallDataLoad(s5);
      var s7 := PushN(s6, 2, 0x0160);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x44);
      var s10 := CallDataLoad(s9);
      var s11 := PushN(s10, 2, 0x0180);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 1, 0x20);
      var s14 := PushN(s13, 2, 0x02a0);
      var s15 := PushN(s14, 1, 0x84);
      var s16 := PushN(s15, 4, 0x3883e119);
      var s17 := PushN(s16, 2, 0x01c0);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 2, 0x0140);
      var s20 := MLoad(s19);
      var s21 := PushN(s20, 2, 0x01e0);
      var s22 := MStore(s21);
      var s23 := PushN(s22, 2, 0x0160);
      var s24 := MLoad(s23);
      var s25 := PushN(s24, 2, 0x0200);
      var s26 := MStore(s25);
      var s27 := PushN(s26, 2, 0x0180);
      var s28 := MLoad(s27);
      var s29 := PushN(s28, 2, 0x0220);
      var s30 := MStore(s29);
      var s31 := PushN(s30, 1, 0xa4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s266(s31, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 253
    * Starting at 0x15a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataLoad(s0);
      var s2 := PushN(s1, 2, 0x0240);
      assert s2.stack[0] == 0x240;
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x01dc);
      var s5 := PushN(s4, 1, 0x0a);
      var s6 := SLoad(s5);
      var s7 := Gas(s6);
      var s8 := StaticCall(s7);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x17ce);
      assert s10.stack[0] == 0x17ce;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s11, gas - 1)
      else
        ExecuteFromCFGNode_s267(s11, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 254
    * Starting at 0x15ba
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s268(s6, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 255
    * Starting at 0x15c3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x02a0);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x01a0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x01a0);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x01c0);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x64);
      var s12 := CallDataLoad(s11);
      var s13 := PushN(s12, 2, 0x01e0);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 1, 0x84);
      var s16 := CallDataLoad(s15);
      var s17 := PushN(s16, 2, 0x0200);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 1, 0x20);
      var s20 := PushN(s19, 2, 0x0300);
      var s21 := PushN(s20, 1, 0x84);
      var s22 := PushN(s21, 4, 0x3883e119);
      var s23 := PushN(s22, 2, 0x0220);
      var s24 := MStore(s23);
      var s25 := PushN(s24, 2, 0x01c0);
      var s26 := MLoad(s25);
      var s27 := PushN(s26, 2, 0x0240);
      assert s27.stack[0] == 0x240;
      var s28 := MStore(s27);
      var s29 := PushN(s28, 2, 0x01e0);
      var s30 := MLoad(s29);
      var s31 := PushN(s30, 2, 0x0260);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s269(s31, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 256
    * Starting at 0x1603
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1603 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      var s2 := PushN(s1, 2, 0x0200);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0280);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0xa4);
      var s7 := CallDataLoad(s6);
      var s8 := PushN(s7, 2, 0x02a0);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x023c);
      var s11 := PushN(s10, 1, 0x09);
      var s12 := SLoad(s11);
      var s13 := Gas(s12);
      var s14 := StaticCall(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x17ce);
      assert s16.stack[0] == 0x17ce;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s17, gas - 1)
      else
        ExecuteFromCFGNode_s270(s17, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 257
    * Starting at 0x1620
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1620 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s271(s6, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 258
    * Starting at 0x1629
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1629 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0300);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := Return(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 272
    * Segment Id for this node is: 259
    * Starting at 0x1638
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1638 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x4fb08c5e);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x172e);
      assert s6.stack[0] == 0x172e;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s284(s7, gas - 1)
      else
        ExecuteFromCFGNode_s273(s7, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 260
    * Starting at 0x1645
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1645 as nat
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
      var s5 := PushN(s4, 2, 0x16a2);
      assert s5.stack[0] == 0x16a2;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s278(s6, gas - 1)
      else
        ExecuteFromCFGNode_s274(s6, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 261
    * Starting at 0x164f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x164f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 2, 0x01e0);
      var s3 := PushN(s2, 1, 0x44);
      var s4 := PushN(s3, 4, 0x4fb08c5e);
      var s5 := PushN(s4, 2, 0x0140);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x04);
      var s8 := CallDataLoad(s7);
      var s9 := PushN(s8, 2, 0x0160);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x24);
      var s12 := CallDataLoad(s11);
      var s13 := PushN(s12, 1, 0x02);
      var s14 := Dup(s13, 1);
      var s15 := Dup(s14, 3);
      var s16 := Lt(s15);
      var s17 := PushN(s16, 2, 0x17ce);
      assert s17.stack[0] == 0x17ce;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s18, gas - 1)
      else
        ExecuteFromCFGNode_s275(s18, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 262
    * Starting at 0x1672
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1672 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

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
      var s10 := PushN(s9, 2, 0x015c);
      var s11 := PushN(s10, 1, 0x09);
      var s12 := SLoad(s11);
      var s13 := Gas(s12);
      var s14 := StaticCall(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x17ce);
      assert s16.stack[0] == 0x17ce;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s17, gas - 1)
      else
        ExecuteFromCFGNode_s276(s17, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 263
    * Starting at 0x168a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x168a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s277(s6, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 264
    * Starting at 0x1693
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1693 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x01e0);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := Return(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 278
    * Segment Id for this node is: 265
    * Starting at 0x16a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x0200);
      var s4 := PushN(s3, 1, 0x44);
      var s5 := PushN(s4, 4, 0x4fb08c5e);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x04);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 2, 0x0180);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 1, 0x00);
      var s13 := PushN(s12, 2, 0x01a0);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 2, 0x017c);
      var s16 := PushN(s15, 1, 0x09);
      var s17 := SLoad(s16);
      var s18 := Gas(s17);
      var s19 := StaticCall(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x17ce);
      assert s21.stack[0] == 0x17ce;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s22, gas - 1)
      else
        ExecuteFromCFGNode_s279(s22, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 266
    * Starting at 0x16cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s280(s6, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 267
    * Starting at 0x16d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0200);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0140);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 2, 0x0200);
      var s9 := PushN(s8, 1, 0x44);
      var s10 := PushN(s9, 4, 0xcc2b27d7);
      var s11 := PushN(s10, 2, 0x0160);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 2, 0x0140);
      var s14 := MLoad(s13);
      var s15 := PushN(s14, 2, 0x0180);
      var s16 := MStore(s15);
      var s17 := PushN(s16, 1, 0x24);
      var s18 := CallDataLoad(s17);
      var s19 := PushN(s18, 1, 0x40);
      var s20 := MLoad(s19);
      var s21 := Dup(s20, 2);
      var s22 := Gt(s21);
      var s23 := PushN(s22, 2, 0x17ce);
      assert s23.stack[0] == 0x17ce;
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s24, gas - 1)
      else
        ExecuteFromCFGNode_s281(s24, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 268
    * Starting at 0x1705
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1705 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01a0);
      var s2 := MStore(s1);
      var s3 := PushN(s2, 2, 0x017c);
      var s4 := PushN(s3, 1, 0x0a);
      var s5 := SLoad(s4);
      var s6 := Gas(s5);
      var s7 := StaticCall(s6);
      var s8 := IsZero(s7);
      var s9 := PushN(s8, 2, 0x17ce);
      assert s9.stack[0] == 0x17ce;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s10, gas - 1)
      else
        ExecuteFromCFGNode_s282(s10, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 269
    * Starting at 0x1716
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1716 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x1f);
      var s2 := ReturnDataSize(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x17ce);
      assert s5.stack[0] == 0x17ce;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s6, gas - 1)
      else
        ExecuteFromCFGNode_s283(s6, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 270
    * Starting at 0x171f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x171f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0200);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := Return(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 284
    * Segment Id for this node is: 271
    * Starting at 0x172e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x172e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xc6610657);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1756);
      assert s6.stack[0] == 0x1756;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s287(s7, gas - 1)
      else
        ExecuteFromCFGNode_s285(s7, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 272
    * Starting at 0x173b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x173b as nat
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
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s9, gas - 1)
      else
        ExecuteFromCFGNode_s286(s9, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 273
    * Starting at 0x1749
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1749 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x01);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := Return(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 287
    * Segment Id for this node is: 274
    * Starting at 0x1756
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1756 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xb9947eb0);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x177e);
      assert s6.stack[0] == 0x177e;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s290(s7, gas - 1)
      else
        ExecuteFromCFGNode_s288(s7, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 275
    * Starting at 0x1763
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1763 as nat
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
      var s8 := PushN(s7, 2, 0x17ce);
      assert s8.stack[0] == 0x17ce;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s9, gas - 1)
      else
        ExecuteFromCFGNode_s289(s9, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 276
    * Starting at 0x1771
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1771 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := Return(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 290
    * Segment Id for this node is: 277
    * Starting at 0x177e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x177e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x16f0115b);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x1796);
      assert s6.stack[0] == 0x1796;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s292(s7, gas - 1)
      else
        ExecuteFromCFGNode_s291(s7, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 278
    * Starting at 0x178b
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x178b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x09);
      var s2 := SLoad(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 292
    * Segment Id for this node is: 279
    * Starting at 0x1796
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1796 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x5d6362bb);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x17ae);
      assert s6.stack[0] == 0x17ae;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s294(s7, gas - 1)
      else
        ExecuteFromCFGNode_s293(s7, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 280
    * Starting at 0x17a3
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x0a);
      var s2 := SLoad(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 294
    * Segment Id for this node is: 281
    * Starting at 0x17ae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xfc0c546a);
      var s3 := Dup(s2, 2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x17c6);
      assert s6.stack[0] == 0x17c6;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s296(s7, gas - 1)
      else
        ExecuteFromCFGNode_s295(s7, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 282
    * Starting at 0x17bb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x0b);
      var s2 := SLoad(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 296
    * Segment Id for this node is: 283
    * Starting at 0x17c6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c6 as nat
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
