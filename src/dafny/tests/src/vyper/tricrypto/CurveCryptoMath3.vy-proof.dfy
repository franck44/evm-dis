
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
      var s1 := PushN(s0, 2, 0x16e0);
      assert s1.stack[0] == 0x16e0;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s2(s2, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 289
    * Starting at 0x16e0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16e0 as nat
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
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s10, gas - 1)
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
      var s1 := PushN(s0, 4, 0xbad1dc26);
      var s2 := Dup(s1, 2);
      var s3 := Xor(s2);
      var s4 := PushN(s3, 2, 0x0032);
      assert s4.stack[0] == 0x32;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s5, gas - 1)
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
      var s1 := PushN(s0, 1, 0x01);
      var s2 := PushN(s1, 2, 0x0400);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x004d);
      assert s4.stack[0] == 0x4d;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 8
    * Starting at 0x4d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 2, 0x0240);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x24);
      var s7 := CallDataLoad(s6);
      var s8 := PushN(s7, 2, 0x0260);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x44);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 2, 0x0280);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 2, 0x0400);
      var s15 := MLoad(s14);
      var s16 := PushN(s15, 2, 0x02a0);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 2, 0x0075);
      assert s18.stack[0] == 0x75;
      var s19 := PushN(s18, 2, 0x0420);
      assert s19.stack[1] == 0x75;
      var s20 := PushN(s19, 2, 0x1807);
      assert s20.stack[0] == 0x1807;
      assert s20.stack[2] == 0x75;
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s7(s21, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 305
    * Starting at 0x1807
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1807 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x75;
      var s2 := PushN(s1, 2, 0x0240);
      assert s2.stack[2] == 0x75;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x75;
      var s4 := PushN(s3, 2, 0x02c0);
      assert s4.stack[3] == 0x75;
      var s5 := MStore(s4);
      assert s5.stack[1] == 0x75;
      var s6 := PushN(s5, 2, 0x0260);
      assert s6.stack[2] == 0x75;
      var s7 := MLoad(s6);
      assert s7.stack[2] == 0x75;
      var s8 := PushN(s7, 2, 0x02e0);
      assert s8.stack[3] == 0x75;
      var s9 := MStore(s8);
      assert s9.stack[1] == 0x75;
      var s10 := PushN(s9, 2, 0x0280);
      assert s10.stack[2] == 0x75;
      var s11 := MLoad(s10);
      assert s11.stack[2] == 0x75;
      var s12 := PushN(s11, 2, 0x0300);
      assert s12.stack[3] == 0x75;
      var s13 := MStore(s12);
      assert s13.stack[1] == 0x75;
      var s14 := PushN(s13, 2, 0x02a0);
      assert s14.stack[2] == 0x75;
      var s15 := MLoad(s14);
      assert s15.stack[2] == 0x75;
      var s16 := IsZero(s15);
      assert s16.stack[2] == 0x75;
      var s17 := PushN(s16, 2, 0x1867);
      assert s17.stack[0] == 0x1867;
      assert s17.stack[3] == 0x75;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s20(s18, gas - 1)
      else
        ExecuteFromCFGNode_s8(s18, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 306
    * Starting at 0x1829
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1829 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x02c0);
      assert s1.stack[2] == 0x75;
      var s2 := MLoad(s1);
      assert s2.stack[2] == 0x75;
      var s3 := PushN(s2, 1, 0xe0);
      assert s3.stack[3] == 0x75;
      var s4 := MStore(s3);
      assert s4.stack[1] == 0x75;
      var s5 := PushN(s4, 2, 0x02e0);
      assert s5.stack[2] == 0x75;
      var s6 := MLoad(s5);
      assert s6.stack[2] == 0x75;
      var s7 := PushN(s6, 2, 0x0100);
      assert s7.stack[3] == 0x75;
      var s8 := MStore(s7);
      assert s8.stack[1] == 0x75;
      var s9 := PushN(s8, 2, 0x0300);
      assert s9.stack[2] == 0x75;
      var s10 := MLoad(s9);
      assert s10.stack[2] == 0x75;
      var s11 := PushN(s10, 2, 0x0120);
      assert s11.stack[3] == 0x75;
      var s12 := MStore(s11);
      assert s12.stack[1] == 0x75;
      var s13 := PushN(s12, 2, 0x184a);
      assert s13.stack[0] == 0x184a;
      assert s13.stack[2] == 0x75;
      var s14 := PushN(s13, 2, 0x0320);
      assert s14.stack[1] == 0x184a;
      assert s14.stack[3] == 0x75;
      var s15 := PushN(s14, 2, 0x16e6);
      assert s15.stack[0] == 0x16e6;
      assert s15.stack[2] == 0x184a;
      assert s15.stack[4] == 0x75;
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s16, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 290
    * Starting at 0x16e6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x184a

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x184a;
      assert s1.stack[3] == 0x75;
      var s2 := PushN(s1, 1, 0xe0);
      assert s2.stack[2] == 0x184a;
      assert s2.stack[4] == 0x75;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x184a;
      assert s3.stack[4] == 0x75;
      var s4 := PushN(s3, 2, 0x0140);
      assert s4.stack[3] == 0x184a;
      assert s4.stack[5] == 0x75;
      var s5 := MStore(s4);
      assert s5.stack[1] == 0x184a;
      assert s5.stack[3] == 0x75;
      var s6 := PushN(s5, 2, 0x0100);
      assert s6.stack[2] == 0x184a;
      assert s6.stack[4] == 0x75;
      var s7 := MLoad(s6);
      assert s7.stack[2] == 0x184a;
      assert s7.stack[4] == 0x75;
      var s8 := PushN(s7, 2, 0x0160);
      assert s8.stack[3] == 0x184a;
      assert s8.stack[5] == 0x75;
      var s9 := MStore(s8);
      assert s9.stack[1] == 0x184a;
      assert s9.stack[3] == 0x75;
      var s10 := PushN(s9, 2, 0x0120);
      assert s10.stack[2] == 0x184a;
      assert s10.stack[4] == 0x75;
      var s11 := MLoad(s10);
      assert s11.stack[2] == 0x184a;
      assert s11.stack[4] == 0x75;
      var s12 := PushN(s11, 2, 0x0180);
      assert s12.stack[3] == 0x184a;
      assert s12.stack[5] == 0x75;
      var s13 := MStore(s12);
      assert s13.stack[1] == 0x184a;
      assert s13.stack[3] == 0x75;
      var s14 := PushN(s13, 2, 0x01a0);
      assert s14.stack[2] == 0x184a;
      assert s14.stack[4] == 0x75;
      var s15 := PushN(s14, 1, 0x01);
      assert s15.stack[3] == 0x184a;
      assert s15.stack[5] == 0x75;
      var s16 := PushN(s15, 1, 0x02);
      assert s16.stack[4] == 0x184a;
      assert s16.stack[6] == 0x75;
      var s17 := Dup(s16, 2);
      assert s17.stack[5] == 0x184a;
      assert s17.stack[7] == 0x75;
      var s18 := Dup(s17, 4);
      assert s18.stack[6] == 0x184a;
      assert s18.stack[8] == 0x75;
      var s19 := MStore(s18);
      assert s19.stack[4] == 0x184a;
      assert s19.stack[6] == 0x75;
      var s20 := Add(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s10(s20, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 291
    * Starting at 0x1709
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1709 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x184a

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x184a;
      assert s1.stack[5] == 0x75;
      var s2 := PushN(s1, 2, 0x0140);
      assert s2.stack[4] == 0x184a;
      assert s2.stack[6] == 0x75;
      var s3 := PushN(s2, 2, 0x01a0);
      assert s3.stack[5] == 0x184a;
      assert s3.stack[7] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[5] == 0x184a;
      assert s4.stack[7] == 0x75;
      var s5 := PushN(s4, 1, 0x03);
      assert s5.stack[6] == 0x184a;
      assert s5.stack[8] == 0x75;
      var s6 := Dup(s5, 2);
      assert s6.stack[7] == 0x184a;
      assert s6.stack[9] == 0x75;
      var s7 := Lt(s6);
      assert s7.stack[6] == 0x184a;
      assert s7.stack[8] == 0x75;
      var s8 := IsZero(s7);
      assert s8.stack[6] == 0x184a;
      assert s8.stack[8] == 0x75;
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      assert s9.stack[7] == 0x184a;
      assert s9.stack[9] == 0x75;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s10, gas - 1)
      else
        ExecuteFromCFGNode_s11(s10, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 292
    * Starting at 0x171a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x171a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[6] == 0x184a;
      assert s1.stack[8] == 0x75;
      var s2 := Mul(s1);
      assert s2.stack[5] == 0x184a;
      assert s2.stack[7] == 0x75;
      var s3 := Add(s2);
      assert s3.stack[4] == 0x184a;
      assert s3.stack[6] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[4] == 0x184a;
      assert s4.stack[6] == 0x75;
      var s5 := PushN(s4, 2, 0x01c0);
      assert s5.stack[5] == 0x184a;
      assert s5.stack[7] == 0x75;
      var s6 := MStore(s5);
      assert s6.stack[3] == 0x184a;
      assert s6.stack[5] == 0x75;
      var s7 := PushN(s6, 2, 0x01a0);
      assert s7.stack[4] == 0x184a;
      assert s7.stack[6] == 0x75;
      var s8 := MLoad(s7);
      assert s8.stack[4] == 0x184a;
      assert s8.stack[6] == 0x75;
      var s9 := PushN(s8, 2, 0x01e0);
      assert s9.stack[5] == 0x184a;
      assert s9.stack[7] == 0x75;
      var s10 := MStore(s9);
      assert s10.stack[3] == 0x184a;
      assert s10.stack[5] == 0x75;
      var s11 := PushN(s10, 2, 0x0200);
      assert s11.stack[4] == 0x184a;
      assert s11.stack[6] == 0x75;
      var s12 := PushN(s11, 1, 0x00);
      assert s12.stack[5] == 0x184a;
      assert s12.stack[7] == 0x75;
      var s13 := PushN(s12, 1, 0x03);
      assert s13.stack[6] == 0x184a;
      assert s13.stack[8] == 0x75;
      var s14 := Dup(s13, 2);
      assert s14.stack[7] == 0x184a;
      assert s14.stack[9] == 0x75;
      var s15 := Dup(s14, 4);
      assert s15.stack[8] == 0x184a;
      assert s15.stack[10] == 0x75;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0x184a;
      assert s16.stack[8] == 0x75;
      var s17 := Add(s16);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s12(s17, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 293
    * Starting at 0x1736
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1736 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x184a;
      assert s1.stack[7] == 0x75;
      var s2 := PushN(s1, 2, 0x0140);
      assert s2.stack[6] == 0x184a;
      assert s2.stack[8] == 0x75;
      var s3 := PushN(s2, 2, 0x01e0);
      assert s3.stack[7] == 0x184a;
      assert s3.stack[9] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[7] == 0x184a;
      assert s4.stack[9] == 0x75;
      var s5 := PushN(s4, 1, 0x01);
      assert s5.stack[8] == 0x184a;
      assert s5.stack[10] == 0x75;
      var s6 := Dup(s5, 1);
      assert s6.stack[9] == 0x184a;
      assert s6.stack[11] == 0x75;
      var s7 := Dup(s6, 3);
      assert s7.stack[10] == 0x184a;
      assert s7.stack[12] == 0x75;
      var s8 := Lt(s7);
      assert s8.stack[9] == 0x184a;
      assert s8.stack[11] == 0x75;
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      assert s9.stack[10] == 0x184a;
      assert s9.stack[12] == 0x75;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s10, gas - 1)
      else
        ExecuteFromCFGNode_s13(s10, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 294
    * Starting at 0x1747
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1747 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x184a

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[9] == 0x184a;
      assert s1.stack[11] == 0x75;
      var s2 := Dup(s1, 3);
      assert s2.stack[10] == 0x184a;
      assert s2.stack[12] == 0x75;
      var s3 := Sub(s2);
      assert s3.stack[9] == 0x184a;
      assert s3.stack[11] == 0x75;
      var s4 := Swap(s3, 1);
      assert s4.stack[9] == 0x184a;
      assert s4.stack[11] == 0x75;
      var s5 := Pop(s4);
      assert s5.stack[8] == 0x184a;
      assert s5.stack[10] == 0x75;
      var s6 := Swap(s5, 1);
      assert s6.stack[8] == 0x184a;
      assert s6.stack[10] == 0x75;
      var s7 := Pop(s6);
      assert s7.stack[7] == 0x184a;
      assert s7.stack[9] == 0x75;
      var s8 := PushN(s7, 1, 0x03);
      assert s8.stack[8] == 0x184a;
      assert s8.stack[10] == 0x75;
      var s9 := Dup(s8, 2);
      assert s9.stack[9] == 0x184a;
      assert s9.stack[11] == 0x75;
      var s10 := Lt(s9);
      assert s10.stack[8] == 0x184a;
      assert s10.stack[10] == 0x75;
      var s11 := IsZero(s10);
      assert s11.stack[8] == 0x184a;
      assert s11.stack[10] == 0x75;
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      assert s12.stack[9] == 0x184a;
      assert s12.stack[11] == 0x75;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s13, gas - 1)
      else
        ExecuteFromCFGNode_s14(s13, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 295
    * Starting at 0x1757
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1757 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x184a

    requires s0.stack[9] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[8] == 0x184a;
      assert s1.stack[10] == 0x75;
      var s2 := Mul(s1);
      assert s2.stack[7] == 0x184a;
      assert s2.stack[9] == 0x75;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x184a;
      assert s3.stack[8] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[6] == 0x184a;
      assert s4.stack[8] == 0x75;
      var s5 := PushN(s4, 2, 0x0220);
      assert s5.stack[7] == 0x184a;
      assert s5.stack[9] == 0x75;
      var s6 := MStore(s5);
      assert s6.stack[5] == 0x184a;
      assert s6.stack[7] == 0x75;
      var s7 := PushN(s6, 2, 0x01c0);
      assert s7.stack[6] == 0x184a;
      assert s7.stack[8] == 0x75;
      var s8 := MLoad(s7);
      assert s8.stack[6] == 0x184a;
      assert s8.stack[8] == 0x75;
      var s9 := PushN(s8, 2, 0x0220);
      assert s9.stack[7] == 0x184a;
      assert s9.stack[9] == 0x75;
      var s10 := MLoad(s9);
      assert s10.stack[7] == 0x184a;
      assert s10.stack[9] == 0x75;
      var s11 := Gt(s10);
      assert s11.stack[6] == 0x184a;
      assert s11.stack[8] == 0x75;
      var s12 := IsZero(s11);
      assert s12.stack[6] == 0x184a;
      assert s12.stack[8] == 0x75;
      var s13 := PushN(s12, 2, 0x1772);
      assert s13.stack[0] == 0x1772;
      assert s13.stack[7] == 0x184a;
      assert s13.stack[9] == 0x75;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s14, gas - 1)
      else
        ExecuteFromCFGNode_s15(s14, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 296
    * Starting at 0x176e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x176e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x17c0);
      assert s1.stack[0] == 0x17c0;
      assert s1.stack[6] == 0x184a;
      assert s1.stack[8] == 0x75;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s2, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 302
    * Starting at 0x17c0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x184a;
      assert s1.stack[7] == 0x75;
      var s2 := Pop(s1);
      assert s2.stack[4] == 0x184a;
      assert s2.stack[6] == 0x75;
      var s3 := Pop(s2);
      assert s3.stack[3] == 0x184a;
      assert s3.stack[5] == 0x75;
      var s4 := PushN(s3, 2, 0x01c0);
      assert s4.stack[4] == 0x184a;
      assert s4.stack[6] == 0x75;
      var s5 := MLoad(s4);
      assert s5.stack[4] == 0x184a;
      assert s5.stack[6] == 0x75;
      var s6 := PushN(s5, 2, 0x0140);
      assert s6.stack[5] == 0x184a;
      assert s6.stack[7] == 0x75;
      var s7 := PushN(s6, 2, 0x01e0);
      assert s7.stack[6] == 0x184a;
      assert s7.stack[8] == 0x75;
      var s8 := MLoad(s7);
      assert s8.stack[6] == 0x184a;
      assert s8.stack[8] == 0x75;
      var s9 := PushN(s8, 1, 0x03);
      assert s9.stack[7] == 0x184a;
      assert s9.stack[9] == 0x75;
      var s10 := Dup(s9, 2);
      assert s10.stack[8] == 0x184a;
      assert s10.stack[10] == 0x75;
      var s11 := Lt(s10);
      assert s11.stack[7] == 0x184a;
      assert s11.stack[9] == 0x75;
      var s12 := IsZero(s11);
      assert s12.stack[7] == 0x184a;
      assert s12.stack[9] == 0x75;
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      assert s13.stack[8] == 0x184a;
      assert s13.stack[10] == 0x75;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s14, gas - 1)
      else
        ExecuteFromCFGNode_s17(s14, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 303
    * Starting at 0x17d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x184a

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[7] == 0x184a;
      assert s1.stack[9] == 0x75;
      var s2 := Mul(s1);
      assert s2.stack[6] == 0x184a;
      assert s2.stack[8] == 0x75;
      var s3 := Add(s2);
      assert s3.stack[5] == 0x184a;
      assert s3.stack[7] == 0x75;
      var s4 := MStore(s3);
      assert s4.stack[3] == 0x184a;
      assert s4.stack[5] == 0x75;
      var s5 := Dup(s4, 2);
      assert s5.stack[4] == 0x184a;
      assert s5.stack[6] == 0x75;
      var s6 := MLoad(s5);
      assert s6.stack[4] == 0x184a;
      assert s6.stack[6] == 0x75;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[5] == 0x184a;
      assert s7.stack[7] == 0x75;
      var s8 := Add(s7);
      assert s8.stack[4] == 0x184a;
      assert s8.stack[6] == 0x75;
      var s9 := Dup(s8, 1);
      assert s9.stack[5] == 0x184a;
      assert s9.stack[7] == 0x75;
      var s10 := Dup(s9, 4);
      assert s10.stack[6] == 0x184a;
      assert s10.stack[8] == 0x75;
      var s11 := MStore(s10);
      assert s11.stack[4] == 0x184a;
      assert s11.stack[6] == 0x75;
      var s12 := Dup(s11, 2);
      assert s12.stack[5] == 0x184a;
      assert s12.stack[7] == 0x75;
      var s13 := Eq(s12);
      assert s13.stack[4] == 0x184a;
      assert s13.stack[6] == 0x75;
      var s14 := IsZero(s13);
      assert s14.stack[4] == 0x184a;
      assert s14.stack[6] == 0x75;
      var s15 := PushN(s14, 2, 0x1709);
      assert s15.stack[0] == 0x1709;
      assert s15.stack[5] == 0x184a;
      assert s15.stack[7] == 0x75;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s16, gas - 1)
      else
        ExecuteFromCFGNode_s18(s16, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 304
    * Starting at 0x17eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x184a

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0x184a;
      assert s1.stack[4] == 0x75;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x184a;
      assert s2.stack[3] == 0x75;
      var s3 := PushN(s2, 2, 0x0140);
      assert s3.stack[2] == 0x184a;
      assert s3.stack[4] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[2] == 0x184a;
      assert s4.stack[4] == 0x75;
      var s5 := Dup(s4, 2);
      assert s5.stack[3] == 0x184a;
      assert s5.stack[5] == 0x75;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0x184a;
      assert s6.stack[3] == 0x75;
      var s7 := PushN(s6, 2, 0x0160);
      assert s7.stack[2] == 0x184a;
      assert s7.stack[4] == 0x75;
      var s8 := MLoad(s7);
      assert s8.stack[2] == 0x184a;
      assert s8.stack[4] == 0x75;
      var s9 := Dup(s8, 2);
      assert s9.stack[3] == 0x184a;
      assert s9.stack[5] == 0x75;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[4] == 0x184a;
      assert s10.stack[6] == 0x75;
      var s11 := Add(s10);
      assert s11.stack[3] == 0x184a;
      assert s11.stack[5] == 0x75;
      var s12 := MStore(s11);
      assert s12.stack[1] == 0x184a;
      assert s12.stack[3] == 0x75;
      var s13 := PushN(s12, 2, 0x0180);
      assert s13.stack[2] == 0x184a;
      assert s13.stack[4] == 0x75;
      var s14 := MLoad(s13);
      assert s14.stack[2] == 0x184a;
      assert s14.stack[4] == 0x75;
      var s15 := Dup(s14, 2);
      assert s15.stack[3] == 0x184a;
      assert s15.stack[5] == 0x75;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[4] == 0x184a;
      assert s16.stack[6] == 0x75;
      var s17 := Add(s16);
      assert s17.stack[3] == 0x184a;
      assert s17.stack[5] == 0x75;
      var s18 := MStore(s17);
      assert s18.stack[1] == 0x184a;
      assert s18.stack[3] == 0x75;
      var s19 := Pop(s18);
      assert s19.stack[0] == 0x184a;
      assert s19.stack[2] == 0x75;
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s20, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 307
    * Starting at 0x184a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x184a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x75;
      var s2 := PushN(s1, 2, 0x0320);
      assert s2.stack[2] == 0x75;
      var s3 := Dup(s2, 1);
      assert s3.stack[3] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[3] == 0x75;
      var s5 := PushN(s4, 2, 0x02c0);
      assert s5.stack[4] == 0x75;
      var s6 := MStore(s5);
      assert s6.stack[2] == 0x75;
      var s7 := Dup(s6, 1);
      assert s7.stack[3] == 0x75;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[4] == 0x75;
      var s9 := Add(s8);
      assert s9.stack[3] == 0x75;
      var s10 := MLoad(s9);
      assert s10.stack[3] == 0x75;
      var s11 := PushN(s10, 2, 0x02e0);
      assert s11.stack[4] == 0x75;
      var s12 := MStore(s11);
      assert s12.stack[2] == 0x75;
      var s13 := Dup(s12, 1);
      assert s13.stack[3] == 0x75;
      var s14 := PushN(s13, 1, 0x40);
      assert s14.stack[4] == 0x75;
      var s15 := Add(s14);
      assert s15.stack[3] == 0x75;
      var s16 := MLoad(s15);
      assert s16.stack[3] == 0x75;
      var s17 := PushN(s16, 2, 0x0300);
      assert s17.stack[4] == 0x75;
      var s18 := MStore(s17);
      assert s18.stack[2] == 0x75;
      var s19 := Pop(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s20(s19, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 308
    * Starting at 0x1867
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1867 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x75;
      var s2 := PushN(s1, 2, 0x02c0);
      assert s2.stack[2] == 0x75;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x75;
      var s4 := PushN(s3, 2, 0x0320);
      assert s4.stack[3] == 0x75;
      var s5 := MStore(s4);
      assert s5.stack[1] == 0x75;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[2] == 0x75;
      var s7 := PushN(s6, 2, 0x0340);
      assert s7.stack[3] == 0x75;
      var s8 := MStore(s7);
      assert s8.stack[1] == 0x75;
      var s9 := PushN(s8, 2, 0x0360);
      assert s9.stack[2] == 0x75;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[3] == 0x75;
      var s11 := PushN(s10, 1, 0xff);
      assert s11.stack[4] == 0x75;
      var s12 := Dup(s11, 2);
      assert s12.stack[5] == 0x75;
      var s13 := Dup(s12, 4);
      assert s13.stack[6] == 0x75;
      var s14 := MStore(s13);
      assert s14.stack[4] == 0x75;
      var s15 := Add(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s21(s15, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 309
    * Starting at 0x1881
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1881 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x75;
      var s2 := PushN(s1, 2, 0x0320);
      assert s2.stack[4] == 0x75;
      var s3 := MLoad(s2);
      assert s3.stack[4] == 0x75;
      var s4 := PushN(s3, 2, 0x0380);
      assert s4.stack[5] == 0x75;
      var s5 := MStore(s4);
      assert s5.stack[3] == 0x75;
      var s6 := PushN(s5, 8, 0x0de0b6b3a7640000);
      assert s6.stack[4] == 0x75;
      var s7 := PushN(s6, 2, 0x03a0);
      assert s7.stack[5] == 0x75;
      var s8 := MStore(s7);
      assert s8.stack[3] == 0x75;
      var s9 := PushN(s8, 2, 0x03e0);
      assert s9.stack[4] == 0x75;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[5] == 0x75;
      var s11 := PushN(s10, 1, 0x03);
      assert s11.stack[6] == 0x75;
      var s12 := Dup(s11, 2);
      assert s12.stack[7] == 0x75;
      var s13 := Dup(s12, 4);
      assert s13.stack[8] == 0x75;
      var s14 := MStore(s13);
      assert s14.stack[6] == 0x75;
      var s15 := Add(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s22(s15, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 310
    * Starting at 0x18a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x75;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[6] == 0x75;
      var s3 := PushN(s2, 2, 0x03e0);
      assert s3.stack[7] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[7] == 0x75;
      var s5 := Mul(s4);
      assert s5.stack[6] == 0x75;
      var s6 := PushN(s5, 2, 0x02c0);
      assert s6.stack[7] == 0x75;
      var s7 := Add(s6);
      assert s7.stack[6] == 0x75;
      var s8 := MLoad(s7);
      assert s8.stack[6] == 0x75;
      var s9 := PushN(s8, 2, 0x03c0);
      assert s9.stack[7] == 0x75;
      var s10 := MStore(s9);
      assert s10.stack[5] == 0x75;
      var s11 := PushN(s10, 2, 0x03a0);
      assert s11.stack[6] == 0x75;
      var s12 := MLoad(s11);
      assert s12.stack[6] == 0x75;
      var s13 := PushN(s12, 2, 0x03c0);
      assert s13.stack[7] == 0x75;
      var s14 := MLoad(s13);
      assert s14.stack[7] == 0x75;
      var s15 := Dup(s14, 1);
      assert s15.stack[8] == 0x75;
      var s16 := Dup(s15, 3);
      assert s16.stack[9] == 0x75;
      var s17 := Mul(s16);
      assert s17.stack[8] == 0x75;
      var s18 := Dup(s17, 3);
      assert s18.stack[9] == 0x75;
      var s19 := IsZero(s18);
      assert s19.stack[9] == 0x75;
      var s20 := Dup(s19, 3);
      assert s20.stack[10] == 0x75;
      var s21 := Dup(s20, 5);
      assert s21.stack[11] == 0x75;
      var s22 := Dup(s21, 4);
      assert s22.stack[12] == 0x75;
      var s23 := Div(s22);
      assert s23.stack[11] == 0x75;
      var s24 := Eq(s23);
      assert s24.stack[10] == 0x75;
      var s25 := Or(s24);
      assert s25.stack[9] == 0x75;
      var s26 := IsZero(s25);
      assert s26.stack[9] == 0x75;
      var s27 := PushN(s26, 2, 0x1a5b);
      assert s27.stack[0] == 0x1a5b;
      assert s27.stack[10] == 0x75;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s46(s28, gas - 1)
      else
        ExecuteFromCFGNode_s23(s28, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 311
    * Starting at 0x18cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[8] == 0x75;
      var s2 := Pop(s1);
      assert s2.stack[7] == 0x75;
      var s3 := Swap(s2, 1);
      assert s3.stack[7] == 0x75;
      var s4 := Pop(s3);
      assert s4.stack[6] == 0x75;
      var s5 := PushN(s4, 2, 0x0320);
      assert s5.stack[7] == 0x75;
      var s6 := MLoad(s5);
      assert s6.stack[7] == 0x75;
      var s7 := Dup(s6, 1);
      assert s7.stack[8] == 0x75;
      var s8 := Dup(s7, 1);
      assert s8.stack[9] == 0x75;
      var s9 := IsZero(s8);
      assert s9.stack[9] == 0x75;
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      assert s10.stack[10] == 0x75;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s46(s11, gas - 1)
      else
        ExecuteFromCFGNode_s24(s11, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 312
    * Starting at 0x18da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[9] == 0x75;
      var s2 := Div(s1);
      assert s2.stack[8] == 0x75;
      var s3 := Swap(s2, 1);
      assert s3.stack[8] == 0x75;
      var s4 := Pop(s3);
      assert s4.stack[7] == 0x75;
      var s5 := Swap(s4, 1);
      assert s5.stack[7] == 0x75;
      var s6 := Pop(s5);
      assert s6.stack[6] == 0x75;
      var s7 := PushN(s6, 2, 0x03a0);
      assert s7.stack[7] == 0x75;
      var s8 := MStore(s7);
      assert s8.stack[5] == 0x75;
      var s9 := Dup(s8, 2);
      assert s9.stack[6] == 0x75;
      var s10 := MLoad(s9);
      assert s10.stack[6] == 0x75;
      var s11 := PushN(s10, 1, 0x01);
      assert s11.stack[7] == 0x75;
      var s12 := Add(s11);
      assert s12.stack[6] == 0x75;
      var s13 := Dup(s12, 1);
      assert s13.stack[7] == 0x75;
      var s14 := Dup(s13, 4);
      assert s14.stack[8] == 0x75;
      var s15 := MStore(s14);
      assert s15.stack[6] == 0x75;
      var s16 := Dup(s15, 2);
      assert s16.stack[7] == 0x75;
      var s17 := Eq(s16);
      assert s17.stack[6] == 0x75;
      var s18 := IsZero(s17);
      assert s18.stack[6] == 0x75;
      var s19 := PushN(s18, 2, 0x18a2);
      assert s19.stack[0] == 0x18a2;
      assert s19.stack[7] == 0x75;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s20, gas - 1)
      else
        ExecuteFromCFGNode_s25(s20, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 313
    * Starting at 0x18f3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[4] == 0x75;
      var s2 := Pop(s1);
      assert s2.stack[3] == 0x75;
      var s3 := PushN(s2, 2, 0x0320);
      assert s3.stack[4] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[4] == 0x75;
      var s5 := PushN(s4, 8, 0x1bc16d674ec80000);
      assert s5.stack[5] == 0x75;
      var s6 := PushN(s5, 2, 0x03a0);
      assert s6.stack[6] == 0x75;
      var s7 := MLoad(s6);
      assert s7.stack[6] == 0x75;
      var s8 := Dup(s7, 2);
      assert s8.stack[7] == 0x75;
      var s9 := Dup(s8, 2);
      assert s9.stack[8] == 0x75;
      var s10 := Dup(s9, 4);
      assert s10.stack[9] == 0x75;
      var s11 := Add(s10);
      assert s11.stack[8] == 0x75;
      var s12 := Lt(s11);
      assert s12.stack[7] == 0x75;
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      assert s13.stack[8] == 0x75;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s14, gas - 1)
      else
        ExecuteFromCFGNode_s26(s14, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 314
    * Starting at 0x190f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x190f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[7] == 0x75;
      var s2 := Dup(s1, 3);
      assert s2.stack[8] == 0x75;
      var s3 := Add(s2);
      assert s3.stack[7] == 0x75;
      var s4 := Swap(s3, 1);
      assert s4.stack[7] == 0x75;
      var s5 := Pop(s4);
      assert s5.stack[6] == 0x75;
      var s6 := Swap(s5, 1);
      assert s6.stack[6] == 0x75;
      var s7 := Pop(s6);
      assert s7.stack[5] == 0x75;
      var s8 := Dup(s7, 1);
      assert s8.stack[6] == 0x75;
      var s9 := Dup(s8, 3);
      assert s9.stack[7] == 0x75;
      var s10 := Mul(s9);
      assert s10.stack[6] == 0x75;
      var s11 := Dup(s10, 3);
      assert s11.stack[7] == 0x75;
      var s12 := IsZero(s11);
      assert s12.stack[7] == 0x75;
      var s13 := Dup(s12, 3);
      assert s13.stack[8] == 0x75;
      var s14 := Dup(s13, 5);
      assert s14.stack[9] == 0x75;
      var s15 := Dup(s14, 4);
      assert s15.stack[10] == 0x75;
      var s16 := Div(s15);
      assert s16.stack[9] == 0x75;
      var s17 := Eq(s16);
      assert s17.stack[8] == 0x75;
      var s18 := Or(s17);
      assert s18.stack[7] == 0x75;
      var s19 := IsZero(s18);
      assert s19.stack[7] == 0x75;
      var s20 := PushN(s19, 2, 0x1a5b);
      assert s20.stack[0] == 0x1a5b;
      assert s20.stack[8] == 0x75;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s21, gas - 1)
      else
        ExecuteFromCFGNode_s27(s21, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 315
    * Starting at 0x1926
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1926 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[6] == 0x75;
      var s2 := Pop(s1);
      assert s2.stack[5] == 0x75;
      var s3 := Swap(s2, 1);
      assert s3.stack[5] == 0x75;
      var s4 := Pop(s3);
      assert s4.stack[4] == 0x75;
      var s5 := PushN(s4, 8, 0x29a2241af62c0000);
      assert s5.stack[5] == 0x75;
      var s6 := Dup(s5, 1);
      assert s6.stack[6] == 0x75;
      var s7 := Dup(s6, 3);
      assert s7.stack[7] == 0x75;
      var s8 := Div(s7);
      assert s8.stack[6] == 0x75;
      var s9 := Swap(s8, 1);
      assert s9.stack[6] == 0x75;
      var s10 := Pop(s9);
      assert s10.stack[5] == 0x75;
      var s11 := Swap(s10, 1);
      assert s11.stack[5] == 0x75;
      var s12 := Pop(s11);
      assert s12.stack[4] == 0x75;
      var s13 := PushN(s12, 2, 0x0320);
      assert s13.stack[5] == 0x75;
      var s14 := MStore(s13);
      assert s14.stack[3] == 0x75;
      var s15 := PushN(s14, 2, 0x0380);
      assert s15.stack[4] == 0x75;
      var s16 := MLoad(s15);
      assert s16.stack[4] == 0x75;
      var s17 := PushN(s16, 2, 0x0320);
      assert s17.stack[5] == 0x75;
      var s18 := MLoad(s17);
      assert s18.stack[5] == 0x75;
      var s19 := Gt(s18);
      assert s19.stack[4] == 0x75;
      var s20 := PushN(s19, 2, 0x1969);
      assert s20.stack[0] == 0x1969;
      assert s20.stack[5] == 0x75;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s21, gas - 1)
      else
        ExecuteFromCFGNode_s28(s21, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 316
    * Starting at 0x194b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x194b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0380);
      assert s1.stack[4] == 0x75;
      var s2 := MLoad(s1);
      assert s2.stack[4] == 0x75;
      var s3 := PushN(s2, 2, 0x0320);
      assert s3.stack[5] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[5] == 0x75;
      var s5 := Dup(s4, 1);
      assert s5.stack[6] == 0x75;
      var s6 := Dup(s5, 3);
      assert s6.stack[7] == 0x75;
      var s7 := Lt(s6);
      assert s7.stack[6] == 0x75;
      var s8 := PushN(s7, 2, 0x1a5b);
      assert s8.stack[0] == 0x1a5b;
      assert s8.stack[7] == 0x75;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s9, gas - 1)
      else
        ExecuteFromCFGNode_s29(s9, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 317
    * Starting at 0x195a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x195a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[6] == 0x75;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0x75;
      var s3 := Sub(s2);
      assert s3.stack[6] == 0x75;
      var s4 := Swap(s3, 1);
      assert s4.stack[6] == 0x75;
      var s5 := Pop(s4);
      assert s5.stack[5] == 0x75;
      var s6 := Swap(s5, 1);
      assert s6.stack[5] == 0x75;
      var s7 := Pop(s6);
      assert s7.stack[4] == 0x75;
      var s8 := PushN(s7, 2, 0x0340);
      assert s8.stack[5] == 0x75;
      var s9 := MStore(s8);
      assert s9.stack[3] == 0x75;
      var s10 := PushN(s9, 2, 0x1984);
      assert s10.stack[0] == 0x1984;
      assert s10.stack[4] == 0x75;
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s11, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 320
    * Starting at 0x1984
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1984 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x75;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[4] == 0x75;
      var s3 := PushN(s2, 2, 0x0340);
      assert s3.stack[5] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[5] == 0x75;
      var s5 := Gt(s4);
      assert s5.stack[4] == 0x75;
      var s6 := IsZero(s5);
      assert s6.stack[4] == 0x75;
      var s7 := PushN(s6, 2, 0x19bb);
      assert s7.stack[0] == 0x19bb;
      assert s7.stack[5] == 0x75;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s8, gas - 1)
      else
        ExecuteFromCFGNode_s31(s8, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 321
    * Starting at 0x1991
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1991 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0320);
      assert s1.stack[4] == 0x75;
      var s2 := MLoad(s1);
      assert s2.stack[4] == 0x75;
      var s3 := PushN(s2, 2, 0x0340);
      assert s3.stack[5] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[5] == 0x75;
      var s5 := PushN(s4, 8, 0x0de0b6b3a7640000);
      assert s5.stack[6] == 0x75;
      var s6 := Dup(s5, 1);
      assert s6.stack[7] == 0x75;
      var s7 := Dup(s6, 3);
      assert s7.stack[8] == 0x75;
      var s8 := Mul(s7);
      assert s8.stack[7] == 0x75;
      var s9 := Dup(s8, 3);
      assert s9.stack[8] == 0x75;
      var s10 := IsZero(s9);
      assert s10.stack[8] == 0x75;
      var s11 := Dup(s10, 3);
      assert s11.stack[9] == 0x75;
      var s12 := Dup(s11, 5);
      assert s12.stack[10] == 0x75;
      var s13 := Dup(s12, 4);
      assert s13.stack[11] == 0x75;
      var s14 := Div(s13);
      assert s14.stack[10] == 0x75;
      var s15 := Eq(s14);
      assert s15.stack[9] == 0x75;
      var s16 := Or(s15);
      assert s16.stack[8] == 0x75;
      var s17 := IsZero(s16);
      assert s17.stack[8] == 0x75;
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      assert s18.stack[9] == 0x75;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s40(s19, gas - 1)
      else
        ExecuteFromCFGNode_s32(s19, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 322
    * Starting at 0x19b2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[7] == 0x75;
      var s2 := Pop(s1);
      assert s2.stack[6] == 0x75;
      var s3 := Swap(s2, 1);
      assert s3.stack[6] == 0x75;
      var s4 := Pop(s3);
      assert s4.stack[5] == 0x75;
      var s5 := Lt(s4);
      assert s5.stack[4] == 0x75;
      var s6 := PushN(s5, 2, 0x19be);
      assert s6.stack[0] == 0x19be;
      assert s6.stack[5] == 0x75;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s7, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 324
    * Starting at 0x19be
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x75;
      var s2 := IsZero(s1);
      assert s2.stack[4] == 0x75;
      var s3 := PushN(s2, 2, 0x19d1);
      assert s3.stack[0] == 0x19d1;
      assert s3.stack[5] == 0x75;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s4, gas - 1)
      else
        ExecuteFromCFGNode_s34(s4, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 325
    * Starting at 0x19c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0x75;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x75;
      var s3 := PushN(s2, 2, 0x0320);
      assert s3.stack[2] == 0x75;
      var s4 := MLoad(s3);
      assert s4.stack[2] == 0x75;
      var s5 := Dup(s4, 2);
      assert s5.stack[3] == 0x75;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0x75;
      var s7 := Pop(s6);
      assert s7.stack[0] == 0x75;
      var s8 := PushN(s7, 2, 0x1a59);
      assert s8.stack[0] == 0x1a59;
      assert s8.stack[1] == 0x75;
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s9, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 329
    * Starting at 0x1a59
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0x75;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s2, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 9
    * Starting at 0x75
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0420);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0440);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x20);
      var s7 := PushN(s6, 2, 0x0440);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 37
    * Segment Id for this node is: 326
    * Starting at 0x19d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x75;
      var s2 := Dup(s1, 2);
      assert s2.stack[4] == 0x75;
      var s3 := MLoad(s2);
      assert s3.stack[4] == 0x75;
      var s4 := PushN(s3, 1, 0x01);
      assert s4.stack[5] == 0x75;
      var s5 := Add(s4);
      assert s5.stack[4] == 0x75;
      var s6 := Dup(s5, 1);
      assert s6.stack[5] == 0x75;
      var s7 := Dup(s6, 4);
      assert s7.stack[6] == 0x75;
      var s8 := MStore(s7);
      assert s8.stack[4] == 0x75;
      var s9 := Dup(s8, 2);
      assert s9.stack[5] == 0x75;
      var s10 := Eq(s9);
      assert s10.stack[4] == 0x75;
      var s11 := IsZero(s10);
      assert s11.stack[4] == 0x75;
      var s12 := PushN(s11, 2, 0x1881);
      assert s12.stack[0] == 0x1881;
      assert s12.stack[5] == 0x75;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s13, gas - 1)
      else
        ExecuteFromCFGNode_s38(s13, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 327
    * Starting at 0x19e1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0x75;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x75;
      var s3 := PushN(s2, 1, 0x10);
      assert s3.stack[2] == 0x75;
      var s4 := PushN(s3, 2, 0x0360);
      assert s4.stack[3] == 0x75;
      var s5 := MStore(s4);
      assert s5.stack[1] == 0x75;
      var s6 := PushN(s5, 32, 0x446964206e6f7420636f6e766572676500000000000000000000000000000000);
      assert s6.stack[2] == 0x75;
      var s7 := PushN(s6, 2, 0x0380);
      assert s7.stack[3] == 0x75;
      var s8 := MStore(s7);
      assert s8.stack[1] == 0x75;
      var s9 := PushN(s8, 2, 0x0360);
      assert s9.stack[2] == 0x75;
      var s10 := Pop(s9);
      assert s10.stack[1] == 0x75;
      var s11 := PushN(s10, 2, 0x0360);
      assert s11.stack[2] == 0x75;
      var s12 := MLoad(s11);
      assert s12.stack[2] == 0x75;
      var s13 := Dup(s12, 1);
      assert s13.stack[3] == 0x75;
      var s14 := PushN(s13, 2, 0x0380);
      assert s14.stack[4] == 0x75;
      var s15 := Add(s14);
      assert s15.stack[3] == 0x75;
      var s16 := Dup(s15, 2);
      assert s16.stack[4] == 0x75;
      var s17 := Dup(s16, 3);
      assert s17.stack[5] == 0x75;
      var s18 := PushN(s17, 1, 0x20);
      assert s18.stack[6] == 0x75;
      var s19 := PushN(s18, 1, 0x01);
      assert s19.stack[7] == 0x75;
      var s20 := Dup(s19, 3);
      assert s20.stack[8] == 0x75;
      var s21 := Sub(s20);
      assert s21.stack[7] == 0x75;
      var s22 := Mod(s21);
      assert s22.stack[6] == 0x75;
      var s23 := PushN(s22, 1, 0x1f);
      assert s23.stack[7] == 0x75;
      var s24 := Dup(s23, 3);
      assert s24.stack[8] == 0x75;
      var s25 := Add(s24);
      assert s25.stack[7] == 0x75;
      var s26 := Sub(s25);
      assert s26.stack[6] == 0x75;
      var s27 := Swap(s26, 1);
      assert s27.stack[6] == 0x75;
      var s28 := Pop(s27);
      assert s28.stack[5] == 0x75;
      var s29 := Sub(s28);
      assert s29.stack[4] == 0x75;
      var s30 := CallDataSize(s29);
      assert s30.stack[5] == 0x75;
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s39(s31, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 328
    * Starting at 0x1a2e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataCopy(s0);
      assert s1.stack[3] == 0x75;
      var s2 := Pop(s1);
      assert s2.stack[2] == 0x75;
      var s3 := Pop(s2);
      assert s3.stack[1] == 0x75;
      var s4 := PushN(s3, 4, 0x08c379a0);
      assert s4.stack[2] == 0x75;
      var s5 := PushN(s4, 2, 0x0320);
      assert s5.stack[3] == 0x75;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0x75;
      var s7 := PushN(s6, 1, 0x20);
      assert s7.stack[2] == 0x75;
      var s8 := PushN(s7, 2, 0x0340);
      assert s8.stack[3] == 0x75;
      var s9 := MStore(s8);
      assert s9.stack[1] == 0x75;
      var s10 := PushN(s9, 2, 0x0360);
      assert s10.stack[2] == 0x75;
      var s11 := MLoad(s10);
      assert s11.stack[2] == 0x75;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[3] == 0x75;
      var s13 := PushN(s12, 1, 0x01);
      assert s13.stack[4] == 0x75;
      var s14 := Dup(s13, 3);
      assert s14.stack[5] == 0x75;
      var s15 := Sub(s14);
      assert s15.stack[4] == 0x75;
      var s16 := Mod(s15);
      assert s16.stack[3] == 0x75;
      var s17 := PushN(s16, 1, 0x1f);
      assert s17.stack[4] == 0x75;
      var s18 := Dup(s17, 3);
      assert s18.stack[5] == 0x75;
      var s19 := Add(s18);
      assert s19.stack[4] == 0x75;
      var s20 := Sub(s19);
      assert s20.stack[3] == 0x75;
      var s21 := Swap(s20, 1);
      assert s21.stack[3] == 0x75;
      var s22 := Pop(s21);
      assert s22.stack[2] == 0x75;
      var s23 := PushN(s22, 1, 0x44);
      assert s23.stack[3] == 0x75;
      var s24 := Add(s23);
      assert s24.stack[2] == 0x75;
      var s25 := PushN(s24, 2, 0x033c);
      assert s25.stack[3] == 0x75;
      var s26 := Revert(s25);
      // Segment is terminal (Revert, Stop or Return)
      s26
  }

  /** Node 40
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x75;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[8] == 0x75;
      var s3 := Dup(s2, 1);
      assert s3.stack[9] == 0x75;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 41
    * Segment Id for this node is: 323
    * Starting at 0x19bb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x75;
      var s2 := PushN(s1, 1, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s33(s2, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x75;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[6] == 0x75;
      var s3 := Dup(s2, 1);
      assert s3.stack[7] == 0x75;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 43
    * Segment Id for this node is: 318
    * Starting at 0x1969
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1969 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x75;
      var s2 := PushN(s1, 2, 0x0320);
      assert s2.stack[4] == 0x75;
      var s3 := MLoad(s2);
      assert s3.stack[4] == 0x75;
      var s4 := PushN(s3, 2, 0x0380);
      assert s4.stack[5] == 0x75;
      var s5 := MLoad(s4);
      assert s5.stack[5] == 0x75;
      var s6 := Dup(s5, 1);
      assert s6.stack[6] == 0x75;
      var s7 := Dup(s6, 3);
      assert s7.stack[7] == 0x75;
      var s8 := Lt(s7);
      assert s8.stack[6] == 0x75;
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      assert s9.stack[7] == 0x75;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s10, gas - 1)
      else
        ExecuteFromCFGNode_s44(s10, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 319
    * Starting at 0x1979
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1979 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[6] == 0x75;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0x75;
      var s3 := Sub(s2);
      assert s3.stack[6] == 0x75;
      var s4 := Swap(s3, 1);
      assert s4.stack[6] == 0x75;
      var s5 := Pop(s4);
      assert s5.stack[5] == 0x75;
      var s6 := Swap(s5, 1);
      assert s6.stack[5] == 0x75;
      var s7 := Pop(s6);
      assert s7.stack[4] == 0x75;
      var s8 := PushN(s7, 2, 0x0340);
      assert s8.stack[5] == 0x75;
      var s9 := MStore(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s30(s9, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x75;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[7] == 0x75;
      var s3 := Dup(s2, 1);
      assert s3.stack[8] == 0x75;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 46
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0x75;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[9] == 0x75;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x75;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 47
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x184a

    requires s0.stack[8] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x184a;
      assert s1.stack[8] == 0x75;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[7] == 0x184a;
      assert s2.stack[9] == 0x75;
      var s3 := Dup(s2, 1);
      assert s3.stack[8] == 0x184a;
      assert s3.stack[10] == 0x75;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 48
    * Segment Id for this node is: 297
    * Starting at 0x1772
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1772 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x184a;
      assert s1.stack[7] == 0x75;
      var s2 := PushN(s1, 2, 0x0220);
      assert s2.stack[6] == 0x184a;
      assert s2.stack[8] == 0x75;
      var s3 := MLoad(s2);
      assert s3.stack[6] == 0x184a;
      assert s3.stack[8] == 0x75;
      var s4 := PushN(s3, 2, 0x0140);
      assert s4.stack[7] == 0x184a;
      assert s4.stack[9] == 0x75;
      var s5 := PushN(s4, 2, 0x01e0);
      assert s5.stack[8] == 0x184a;
      assert s5.stack[10] == 0x75;
      var s6 := MLoad(s5);
      assert s6.stack[8] == 0x184a;
      assert s6.stack[10] == 0x75;
      var s7 := PushN(s6, 1, 0x03);
      assert s7.stack[9] == 0x184a;
      assert s7.stack[11] == 0x75;
      var s8 := Dup(s7, 2);
      assert s8.stack[10] == 0x184a;
      assert s8.stack[12] == 0x75;
      var s9 := Lt(s8);
      assert s9.stack[9] == 0x184a;
      assert s9.stack[11] == 0x75;
      var s10 := IsZero(s9);
      assert s10.stack[9] == 0x184a;
      assert s10.stack[11] == 0x75;
      var s11 := PushN(s10, 2, 0x1a5b);
      assert s11.stack[0] == 0x1a5b;
      assert s11.stack[10] == 0x184a;
      assert s11.stack[12] == 0x75;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s12, gas - 1)
      else
        ExecuteFromCFGNode_s49(s12, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 298
    * Starting at 0x1787
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1787 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x184a

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[9] == 0x184a;
      assert s1.stack[11] == 0x75;
      var s2 := Mul(s1);
      assert s2.stack[8] == 0x184a;
      assert s2.stack[10] == 0x75;
      var s3 := Add(s2);
      assert s3.stack[7] == 0x184a;
      assert s3.stack[9] == 0x75;
      var s4 := MStore(s3);
      assert s4.stack[5] == 0x184a;
      assert s4.stack[7] == 0x75;
      var s5 := PushN(s4, 2, 0x01e0);
      assert s5.stack[6] == 0x184a;
      assert s5.stack[8] == 0x75;
      var s6 := Dup(s5, 1);
      assert s6.stack[7] == 0x184a;
      assert s6.stack[9] == 0x75;
      var s7 := MLoad(s6);
      assert s7.stack[7] == 0x184a;
      assert s7.stack[9] == 0x75;
      var s8 := PushN(s7, 1, 0x01);
      assert s8.stack[8] == 0x184a;
      assert s8.stack[10] == 0x75;
      var s9 := Dup(s8, 1);
      assert s9.stack[9] == 0x184a;
      assert s9.stack[11] == 0x75;
      var s10 := Dup(s9, 3);
      assert s10.stack[10] == 0x184a;
      assert s10.stack[12] == 0x75;
      var s11 := Lt(s10);
      assert s11.stack[9] == 0x184a;
      assert s11.stack[11] == 0x75;
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      assert s12.stack[10] == 0x184a;
      assert s12.stack[12] == 0x75;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s13, gas - 1)
      else
        ExecuteFromCFGNode_s50(s13, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 299
    * Starting at 0x179a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x179a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x184a

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[9] == 0x184a;
      assert s1.stack[11] == 0x75;
      var s2 := Dup(s1, 3);
      assert s2.stack[10] == 0x184a;
      assert s2.stack[12] == 0x75;
      var s3 := Sub(s2);
      assert s3.stack[9] == 0x184a;
      assert s3.stack[11] == 0x75;
      var s4 := Swap(s3, 1);
      assert s4.stack[9] == 0x184a;
      assert s4.stack[11] == 0x75;
      var s5 := Pop(s4);
      assert s5.stack[8] == 0x184a;
      assert s5.stack[10] == 0x75;
      var s6 := Swap(s5, 1);
      assert s6.stack[8] == 0x184a;
      assert s6.stack[10] == 0x75;
      var s7 := Pop(s6);
      assert s7.stack[7] == 0x184a;
      assert s7.stack[9] == 0x75;
      var s8 := Dup(s7, 2);
      assert s8.stack[8] == 0x184a;
      assert s8.stack[10] == 0x75;
      var s9 := MStore(s8);
      assert s9.stack[6] == 0x184a;
      assert s9.stack[8] == 0x75;
      var s10 := Pop(s9);
      assert s10.stack[5] == 0x184a;
      assert s10.stack[7] == 0x75;
      var s11 := PushN(s10, 2, 0x01e0);
      assert s11.stack[6] == 0x184a;
      assert s11.stack[8] == 0x75;
      var s12 := MLoad(s11);
      assert s12.stack[6] == 0x184a;
      assert s12.stack[8] == 0x75;
      var s13 := PushN(s12, 2, 0x17b0);
      assert s13.stack[0] == 0x17b0;
      assert s13.stack[7] == 0x184a;
      assert s13.stack[9] == 0x75;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s14, gas - 1)
      else
        ExecuteFromCFGNode_s51(s14, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 300
    * Starting at 0x17ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x17c0);
      assert s1.stack[0] == 0x17c0;
      assert s1.stack[6] == 0x184a;
      assert s1.stack[8] == 0x75;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s2, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 301
    * Starting at 0x17b0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x184a;
      assert s1.stack[7] == 0x75;
      var s2 := Dup(s1, 2);
      assert s2.stack[6] == 0x184a;
      assert s2.stack[8] == 0x75;
      var s3 := MLoad(s2);
      assert s3.stack[6] == 0x184a;
      assert s3.stack[8] == 0x75;
      var s4 := PushN(s3, 1, 0x01);
      assert s4.stack[7] == 0x184a;
      assert s4.stack[9] == 0x75;
      var s5 := Add(s4);
      assert s5.stack[6] == 0x184a;
      assert s5.stack[8] == 0x75;
      var s6 := Dup(s5, 1);
      assert s6.stack[7] == 0x184a;
      assert s6.stack[9] == 0x75;
      var s7 := Dup(s6, 4);
      assert s7.stack[8] == 0x184a;
      assert s7.stack[10] == 0x75;
      var s8 := MStore(s7);
      assert s8.stack[6] == 0x184a;
      assert s8.stack[8] == 0x75;
      var s9 := Dup(s8, 2);
      assert s9.stack[7] == 0x184a;
      assert s9.stack[9] == 0x75;
      var s10 := Eq(s9);
      assert s10.stack[6] == 0x184a;
      assert s10.stack[8] == 0x75;
      var s11 := IsZero(s10);
      assert s11.stack[6] == 0x184a;
      assert s11.stack[8] == 0x75;
      var s12 := PushN(s11, 2, 0x1736);
      assert s12.stack[0] == 0x1736;
      assert s12.stack[7] == 0x184a;
      assert s12.stack[9] == 0x75;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s13, gas - 1)
      else
        ExecuteFromCFGNode_s16(s13, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x184a

    requires s0.stack[10] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0x184a;
      assert s1.stack[10] == 0x75;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[9] == 0x184a;
      assert s2.stack[11] == 0x75;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x184a;
      assert s3.stack[12] == 0x75;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 54
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x184a

    requires s0.stack[9] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x184a;
      assert s1.stack[9] == 0x75;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[8] == 0x184a;
      assert s2.stack[10] == 0x75;
      var s3 := Dup(s2, 1);
      assert s3.stack[9] == 0x184a;
      assert s3.stack[11] == 0x75;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 55
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x75

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x184a;
      assert s1.stack[7] == 0x75;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[6] == 0x184a;
      assert s2.stack[8] == 0x75;
      var s3 := Dup(s2, 1);
      assert s3.stack[7] == 0x184a;
      assert s3.stack[9] == 0x75;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 56
    * Segment Id for this node is: 5
    * Starting at 0x32
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x39303e24);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x0084);
      assert s5.stack[0] == 0x84;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s6, gas - 1)
      else
        ExecuteFromCFGNode_s57(s6, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 6
    * Starting at 0x3e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x64);
      var s2 := CallDataLoad(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 1, 0x01);
      var s5 := Shr(s4);
      var s6 := PushN(s5, 2, 0x1a5b);
      assert s6.stack[0] == 0x1a5b;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s7, gas - 1)
      else
        ExecuteFromCFGNode_s58(s7, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 7
    * Starting at 0x49
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0400);
      var s2 := MStore(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s6(s2, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
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

  /** Node 60
    * Segment Id for this node is: 10
    * Starting at 0x84
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xfa18042d);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x01d1);
      assert s5.stack[0] == 0x1d1;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s6, gas - 1)
      else
        ExecuteFromCFGNode_s61(s6, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 11
    * Starting at 0x90
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 8, 0x0de0b6b3a7640000);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 1, 0x00);
      var s5 := PushN(s4, 2, 0x0100);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0140);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 1, 0x03);
      var s10 := Dup(s9, 2);
      var s11 := Dup(s10, 4);
      var s12 := MStore(s11);
      var s13 := Add(s12);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s62(s13, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 12
    * Starting at 0xad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MLoad(s3);
      var s5 := Mul(s4);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := PushN(s8, 2, 0x0120);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0100);
      var s12 := Dup(s11, 1);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 2, 0x0120);
      var s15 := MLoad(s14);
      var s16 := Dup(s15, 2);
      var s17 := Dup(s16, 2);
      var s18 := Dup(s17, 4);
      var s19 := Add(s18);
      var s20 := Lt(s19);
      var s21 := PushN(s20, 2, 0x1a5b);
      assert s21.stack[0] == 0x1a5b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s22, gas - 1)
      else
        ExecuteFromCFGNode_s63(s22, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 13
    * Starting at 0xcf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := Dup(s7, 2);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      var s11 := Dup(s10, 2);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 1, 0x01);
      var s14 := Add(s13);
      var s15 := Dup(s14, 1);
      var s16 := Dup(s15, 4);
      var s17 := MStore(s16);
      var s18 := Dup(s17, 2);
      var s19 := Eq(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x00ad);
      assert s21.stack[0] == 0xad;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s62(s22, gas - 1)
      else
        ExecuteFromCFGNode_s64(s22, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 14
    * Starting at 0xe8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := PushN(s3, 1, 0x00);
      var s5 := PushN(s4, 1, 0x03);
      var s6 := Dup(s5, 2);
      var s7 := Dup(s6, 4);
      var s8 := MStore(s7);
      var s9 := Add(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s65(s9, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 15
    * Starting at 0xf5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MLoad(s3);
      var s5 := Mul(s4);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := PushN(s8, 2, 0x0120);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0xe0);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 1, 0x03);
      var s14 := Dup(s13, 1);
      var s15 := Dup(s14, 3);
      var s16 := Mul(s15);
      var s17 := Dup(s16, 3);
      var s18 := IsZero(s17);
      var s19 := Dup(s18, 3);
      var s20 := Dup(s19, 5);
      var s21 := Dup(s20, 4);
      var s22 := Div(s21);
      var s23 := Eq(s22);
      var s24 := Or(s23);
      var s25 := IsZero(s24);
      var s26 := PushN(s25, 2, 0x1a5b);
      assert s26.stack[0] == 0x1a5b;
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s27, gas - 1)
      else
        ExecuteFromCFGNode_s66(s27, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 16
    * Starting at 0x11a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0120);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 3);
      var s9 := Mul(s8);
      var s10 := Dup(s9, 3);
      var s11 := IsZero(s10);
      var s12 := Dup(s11, 3);
      var s13 := Dup(s12, 5);
      var s14 := Dup(s13, 4);
      var s15 := Div(s14);
      var s16 := Eq(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x1a5b);
      assert s19.stack[0] == 0x1a5b;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s20, gas - 1)
      else
        ExecuteFromCFGNode_s67(s20, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 17
    * Starting at 0x132
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0100);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s68(s11, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 18
    * Starting at 0x141
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x141 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 1, 0xe0);
      var s8 := MStore(s7);
      var s9 := Dup(s8, 2);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 1, 0x01);
      var s12 := Add(s11);
      var s13 := Dup(s12, 1);
      var s14 := Dup(s13, 4);
      var s15 := MStore(s14);
      var s16 := Dup(s15, 2);
      var s17 := Eq(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x00f5);
      assert s19.stack[0] == 0xf5;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s20, gas - 1)
      else
        ExecuteFromCFGNode_s69(s20, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 19
    * Starting at 0x159
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x159 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 1, 0x64);
      var s5 := CallDataLoad(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x01c3);
      assert s8.stack[0] == 0x1c3;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s9, gas - 1)
      else
        ExecuteFromCFGNode_s70(s9, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 20
    * Starting at 0x166
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x166 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x64);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 8, 0x0de0b6b3a7640000);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := Mul(s5);
      var s7 := Dup(s6, 3);
      var s8 := IsZero(s7);
      var s9 := Dup(s8, 3);
      var s10 := Dup(s9, 5);
      var s11 := Dup(s10, 4);
      var s12 := Div(s11);
      var s13 := Eq(s12);
      var s14 := Or(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x1a5b);
      assert s16.stack[0] == 0x1a5b;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s17, gas - 1)
      else
        ExecuteFromCFGNode_s71(s17, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 21
    * Starting at 0x182
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x182 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x64);
      var s6 := CallDataLoad(s5);
      var s7 := PushN(s6, 8, 0x0de0b6b3a7640000);
      var s8 := Dup(s7, 2);
      var s9 := Dup(s8, 2);
      var s10 := Dup(s9, 4);
      var s11 := Add(s10);
      var s12 := Lt(s11);
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s14, gas - 1)
      else
        ExecuteFromCFGNode_s72(s14, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 22
    * Starting at 0x19b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 1, 0xe0);
      var s9 := MLoad(s8);
      var s10 := Dup(s9, 1);
      var s11 := Dup(s10, 3);
      var s12 := Lt(s11);
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s14, gas - 1)
      else
        ExecuteFromCFGNode_s73(s14, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 23
    * Starting at 0x1ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

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
      var s8 := Dup(s7, 1);
      var s9 := Dup(s8, 1);
      var s10 := IsZero(s9);
      var s11 := PushN(s10, 2, 0x1a5b);
      assert s11.stack[0] == 0x1a5b;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s12, gas - 1)
      else
        ExecuteFromCFGNode_s74(s12, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 24
    * Starting at 0x1ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 1, 0xe0);
      var s8 := MStore(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s75(s8, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 25
    * Starting at 0x1c3
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0120);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x20);
      var s7 := PushN(s6, 2, 0x0120);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 76
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
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

  /** Node 77
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
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

  /** Node 78
    * Segment Id for this node is: 26
    * Starting at 0x1d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xc7fab708);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x0a09);
      assert s5.stack[0] == 0xa09;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s216(s6, gas - 1)
      else
        ExecuteFromCFGNode_s79(s6, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 27
    * Starting at 0x1dd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0a8b);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := Gt(s3);
      var s5 := PushN(s4, 2, 0x01ee);
      assert s5.stack[0] == 0x1ee;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s215(s6, gas - 1)
      else
        ExecuteFromCFGNode_s80(s6, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 28
    * Starting at 0x1e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 2, 0x01f8);
      assert s2.stack[0] == 0x1f8;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s3, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 30
    * Starting at 0x1f8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := IsZero(s1);
      var s3 := PushN(s2, 2, 0x1a5b);
      assert s3.stack[0] == 0x1a5b;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s4, gas - 1)
      else
        ExecuteFromCFGNode_s82(s4, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 31
    * Starting at 0x1fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 5, 0x02540be3ff);
      var s2 := PushN(s1, 1, 0x24);
      var s3 := CallDataLoad(s2);
      var s4 := Gt(s3);
      var s5 := PushN(s4, 2, 0x0212);
      assert s5.stack[0] == 0x212;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s214(s6, gas - 1)
      else
        ExecuteFromCFGNode_s83(s6, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 32
    * Starting at 0x20c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 2, 0x021f);
      assert s2.stack[0] == 0x21f;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s3, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 34
    * Starting at 0x21f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := IsZero(s1);
      var s3 := PushN(s2, 2, 0x1a5b);
      assert s3.stack[0] == 0x1a5b;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s4, gas - 1)
      else
        ExecuteFromCFGNode_s85(s4, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 35
    * Starting at 0x225
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x225 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x44);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x64);
      var s6 := CallDataLoad(s5);
      var s7 := PushN(s6, 2, 0x0100);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x84);
      assert s9.stack[0] == 0x84;
      var s10 := CallDataLoad(s9);
      var s11 := PushN(s10, 2, 0x0120);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 2, 0x0243);
      assert s13.stack[0] == 0x243;
      var s14 := PushN(s13, 2, 0x0460);
      assert s14.stack[1] == 0x243;
      var s15 := PushN(s14, 2, 0x16e6);
      assert s15.stack[0] == 0x16e6;
      assert s15.stack[2] == 0x243;
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s16, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 290
    * Starting at 0x16e6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x243;
      var s2 := PushN(s1, 1, 0xe0);
      assert s2.stack[2] == 0x243;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x243;
      var s4 := PushN(s3, 2, 0x0140);
      assert s4.stack[3] == 0x243;
      var s5 := MStore(s4);
      assert s5.stack[1] == 0x243;
      var s6 := PushN(s5, 2, 0x0100);
      assert s6.stack[2] == 0x243;
      var s7 := MLoad(s6);
      assert s7.stack[2] == 0x243;
      var s8 := PushN(s7, 2, 0x0160);
      assert s8.stack[3] == 0x243;
      var s9 := MStore(s8);
      assert s9.stack[1] == 0x243;
      var s10 := PushN(s9, 2, 0x0120);
      assert s10.stack[2] == 0x243;
      var s11 := MLoad(s10);
      assert s11.stack[2] == 0x243;
      var s12 := PushN(s11, 2, 0x0180);
      assert s12.stack[3] == 0x243;
      var s13 := MStore(s12);
      assert s13.stack[1] == 0x243;
      var s14 := PushN(s13, 2, 0x01a0);
      assert s14.stack[2] == 0x243;
      var s15 := PushN(s14, 1, 0x01);
      assert s15.stack[3] == 0x243;
      var s16 := PushN(s15, 1, 0x02);
      assert s16.stack[4] == 0x243;
      var s17 := Dup(s16, 2);
      assert s17.stack[5] == 0x243;
      var s18 := Dup(s17, 4);
      assert s18.stack[6] == 0x243;
      var s19 := MStore(s18);
      assert s19.stack[4] == 0x243;
      var s20 := Add(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s87(s20, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 291
    * Starting at 0x1709
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1709 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x243;
      var s2 := PushN(s1, 2, 0x0140);
      assert s2.stack[4] == 0x243;
      var s3 := PushN(s2, 2, 0x01a0);
      assert s3.stack[5] == 0x243;
      var s4 := MLoad(s3);
      assert s4.stack[5] == 0x243;
      var s5 := PushN(s4, 1, 0x03);
      assert s5.stack[6] == 0x243;
      var s6 := Dup(s5, 2);
      assert s6.stack[7] == 0x243;
      var s7 := Lt(s6);
      assert s7.stack[6] == 0x243;
      var s8 := IsZero(s7);
      assert s8.stack[6] == 0x243;
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      assert s9.stack[7] == 0x243;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s213(s10, gas - 1)
      else
        ExecuteFromCFGNode_s88(s10, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 292
    * Starting at 0x171a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x171a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[6] == 0x243;
      var s2 := Mul(s1);
      assert s2.stack[5] == 0x243;
      var s3 := Add(s2);
      assert s3.stack[4] == 0x243;
      var s4 := MLoad(s3);
      assert s4.stack[4] == 0x243;
      var s5 := PushN(s4, 2, 0x01c0);
      assert s5.stack[5] == 0x243;
      var s6 := MStore(s5);
      assert s6.stack[3] == 0x243;
      var s7 := PushN(s6, 2, 0x01a0);
      assert s7.stack[4] == 0x243;
      var s8 := MLoad(s7);
      assert s8.stack[4] == 0x243;
      var s9 := PushN(s8, 2, 0x01e0);
      assert s9.stack[5] == 0x243;
      var s10 := MStore(s9);
      assert s10.stack[3] == 0x243;
      var s11 := PushN(s10, 2, 0x0200);
      assert s11.stack[4] == 0x243;
      var s12 := PushN(s11, 1, 0x00);
      assert s12.stack[5] == 0x243;
      var s13 := PushN(s12, 1, 0x03);
      assert s13.stack[6] == 0x243;
      var s14 := Dup(s13, 2);
      assert s14.stack[7] == 0x243;
      var s15 := Dup(s14, 4);
      assert s15.stack[8] == 0x243;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0x243;
      var s17 := Add(s16);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s89(s17, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 293
    * Starting at 0x1736
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1736 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x243;
      var s2 := PushN(s1, 2, 0x0140);
      assert s2.stack[6] == 0x243;
      var s3 := PushN(s2, 2, 0x01e0);
      assert s3.stack[7] == 0x243;
      var s4 := MLoad(s3);
      assert s4.stack[7] == 0x243;
      var s5 := PushN(s4, 1, 0x01);
      assert s5.stack[8] == 0x243;
      var s6 := Dup(s5, 1);
      assert s6.stack[9] == 0x243;
      var s7 := Dup(s6, 3);
      assert s7.stack[10] == 0x243;
      var s8 := Lt(s7);
      assert s8.stack[9] == 0x243;
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      assert s9.stack[10] == 0x243;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s211(s10, gas - 1)
      else
        ExecuteFromCFGNode_s90(s10, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 294
    * Starting at 0x1747
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1747 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[9] == 0x243;
      var s2 := Dup(s1, 3);
      assert s2.stack[10] == 0x243;
      var s3 := Sub(s2);
      assert s3.stack[9] == 0x243;
      var s4 := Swap(s3, 1);
      assert s4.stack[9] == 0x243;
      var s5 := Pop(s4);
      assert s5.stack[8] == 0x243;
      var s6 := Swap(s5, 1);
      assert s6.stack[8] == 0x243;
      var s7 := Pop(s6);
      assert s7.stack[7] == 0x243;
      var s8 := PushN(s7, 1, 0x03);
      assert s8.stack[8] == 0x243;
      var s9 := Dup(s8, 2);
      assert s9.stack[9] == 0x243;
      var s10 := Lt(s9);
      assert s10.stack[8] == 0x243;
      var s11 := IsZero(s10);
      assert s11.stack[8] == 0x243;
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      assert s12.stack[9] == 0x243;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s13, gas - 1)
      else
        ExecuteFromCFGNode_s91(s13, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 295
    * Starting at 0x1757
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1757 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[8] == 0x243;
      var s2 := Mul(s1);
      assert s2.stack[7] == 0x243;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x243;
      var s4 := MLoad(s3);
      assert s4.stack[6] == 0x243;
      var s5 := PushN(s4, 2, 0x0220);
      assert s5.stack[7] == 0x243;
      var s6 := MStore(s5);
      assert s6.stack[5] == 0x243;
      var s7 := PushN(s6, 2, 0x01c0);
      assert s7.stack[6] == 0x243;
      var s8 := MLoad(s7);
      assert s8.stack[6] == 0x243;
      var s9 := PushN(s8, 2, 0x0220);
      assert s9.stack[7] == 0x243;
      var s10 := MLoad(s9);
      assert s10.stack[7] == 0x243;
      var s11 := Gt(s10);
      assert s11.stack[6] == 0x243;
      var s12 := IsZero(s11);
      assert s12.stack[6] == 0x243;
      var s13 := PushN(s12, 2, 0x1772);
      assert s13.stack[0] == 0x1772;
      assert s13.stack[7] == 0x243;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s14, gas - 1)
      else
        ExecuteFromCFGNode_s92(s14, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 296
    * Starting at 0x176e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x176e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x17c0);
      assert s1.stack[0] == 0x17c0;
      assert s1.stack[6] == 0x243;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s2, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 302
    * Starting at 0x17c0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x243;
      var s2 := Pop(s1);
      assert s2.stack[4] == 0x243;
      var s3 := Pop(s2);
      assert s3.stack[3] == 0x243;
      var s4 := PushN(s3, 2, 0x01c0);
      assert s4.stack[4] == 0x243;
      var s5 := MLoad(s4);
      assert s5.stack[4] == 0x243;
      var s6 := PushN(s5, 2, 0x0140);
      assert s6.stack[5] == 0x243;
      var s7 := PushN(s6, 2, 0x01e0);
      assert s7.stack[6] == 0x243;
      var s8 := MLoad(s7);
      assert s8.stack[6] == 0x243;
      var s9 := PushN(s8, 1, 0x03);
      assert s9.stack[7] == 0x243;
      var s10 := Dup(s9, 2);
      assert s10.stack[8] == 0x243;
      var s11 := Lt(s10);
      assert s11.stack[7] == 0x243;
      var s12 := IsZero(s11);
      assert s12.stack[7] == 0x243;
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      assert s13.stack[8] == 0x243;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s205(s14, gas - 1)
      else
        ExecuteFromCFGNode_s94(s14, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 303
    * Starting at 0x17d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[7] == 0x243;
      var s2 := Mul(s1);
      assert s2.stack[6] == 0x243;
      var s3 := Add(s2);
      assert s3.stack[5] == 0x243;
      var s4 := MStore(s3);
      assert s4.stack[3] == 0x243;
      var s5 := Dup(s4, 2);
      assert s5.stack[4] == 0x243;
      var s6 := MLoad(s5);
      assert s6.stack[4] == 0x243;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[5] == 0x243;
      var s8 := Add(s7);
      assert s8.stack[4] == 0x243;
      var s9 := Dup(s8, 1);
      assert s9.stack[5] == 0x243;
      var s10 := Dup(s9, 4);
      assert s10.stack[6] == 0x243;
      var s11 := MStore(s10);
      assert s11.stack[4] == 0x243;
      var s12 := Dup(s11, 2);
      assert s12.stack[5] == 0x243;
      var s13 := Eq(s12);
      assert s13.stack[4] == 0x243;
      var s14 := IsZero(s13);
      assert s14.stack[4] == 0x243;
      var s15 := PushN(s14, 2, 0x1709);
      assert s15.stack[0] == 0x1709;
      assert s15.stack[5] == 0x243;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s16, gas - 1)
      else
        ExecuteFromCFGNode_s95(s16, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 304
    * Starting at 0x17eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0x243;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x243;
      var s3 := PushN(s2, 2, 0x0140);
      assert s3.stack[2] == 0x243;
      var s4 := MLoad(s3);
      assert s4.stack[2] == 0x243;
      var s5 := Dup(s4, 2);
      assert s5.stack[3] == 0x243;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0x243;
      var s7 := PushN(s6, 2, 0x0160);
      assert s7.stack[2] == 0x243;
      var s8 := MLoad(s7);
      assert s8.stack[2] == 0x243;
      var s9 := Dup(s8, 2);
      assert s9.stack[3] == 0x243;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[4] == 0x243;
      var s11 := Add(s10);
      assert s11.stack[3] == 0x243;
      var s12 := MStore(s11);
      assert s12.stack[1] == 0x243;
      var s13 := PushN(s12, 2, 0x0180);
      assert s13.stack[2] == 0x243;
      var s14 := MLoad(s13);
      assert s14.stack[2] == 0x243;
      var s15 := Dup(s14, 2);
      assert s15.stack[3] == 0x243;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[4] == 0x243;
      var s17 := Add(s16);
      assert s17.stack[3] == 0x243;
      var s18 := MStore(s17);
      assert s18.stack[1] == 0x243;
      var s19 := Pop(s18);
      assert s19.stack[0] == 0x243;
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s20, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 36
    * Starting at 0x243
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0460);
      var s3 := Dup(s2, 1);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0400);
      var s6 := MStore(s5);
      var s7 := Dup(s6, 1);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := Add(s8);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x0420);
      var s12 := MStore(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 1, 0x40);
      var s15 := Add(s14);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 2, 0x0440);
      var s18 := MStore(s17);
      var s19 := Pop(s18);
      var s20 := PushN(s19, 4, 0x3b9ac9ff);
      var s21 := PushN(s20, 2, 0x0400);
      var s22 := MLoad(s21);
      var s23 := Gt(s22);
      var s24 := PushN(s23, 2, 0x0274);
      assert s24.stack[0] == 0x274;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s25, gas - 1)
      else
        ExecuteFromCFGNode_s97(s25, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 37
    * Starting at 0x26e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 2, 0x0289);
      assert s2.stack[0] == 0x289;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s3, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 39
    * Starting at 0x289
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x289 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := IsZero(s1);
      var s3 := PushN(s2, 2, 0x1a5b);
      assert s3.stack[0] == 0x1a5b;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s4, gas - 1)
      else
        ExecuteFromCFGNode_s99(s4, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 40
    * Starting at 0x28f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0460);
      var s2 := PushN(s1, 1, 0x01);
      var s3 := PushN(s2, 1, 0x02);
      var s4 := Dup(s3, 2);
      var s5 := Dup(s4, 4);
      var s6 := MStore(s5);
      var s7 := Add(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s100(s7, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 41
    * Starting at 0x29a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0400);
      var s3 := PushN(s2, 2, 0x0460);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x03);
      var s6 := Dup(s5, 2);
      var s7 := Lt(s6);
      var s8 := IsZero(s7);
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s10, gas - 1)
      else
        ExecuteFromCFGNode_s101(s10, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 42
    * Starting at 0x2ab
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := Mul(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 8, 0x0de0b6b3a7640000);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Mul(s7);
      var s9 := Dup(s8, 3);
      var s10 := IsZero(s9);
      var s11 := Dup(s10, 3);
      var s12 := Dup(s11, 5);
      var s13 := Dup(s12, 4);
      var s14 := Div(s13);
      var s15 := Eq(s14);
      var s16 := Or(s15);
      var s17 := IsZero(s16);
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s19, gas - 1)
      else
        ExecuteFromCFGNode_s102(s19, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 43
    * Starting at 0x2c9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0400);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s103(s11, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 44
    * Starting at 0x2d8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0480);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 5, 0x174876e7ff);
      var s10 := PushN(s9, 2, 0x0480);
      var s11 := MLoad(s10);
      var s12 := Gt(s11);
      var s13 := IsZero(s12);
      var s14 := PushN(s13, 2, 0x1a5b);
      assert s14.stack[0] == 0x1a5b;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s15, gas - 1)
      else
        ExecuteFromCFGNode_s104(s15, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 45
    * Starting at 0x2f2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 1, 0x01);
      var s4 := Add(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 4);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 2);
      var s9 := Eq(s8);
      var s10 := IsZero(s9);
      var s11 := PushN(s10, 2, 0x029a);
      assert s11.stack[0] == 0x29a;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s12, gas - 1)
      else
        ExecuteFromCFGNode_s105(s12, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 46
    * Starting at 0x301
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x301 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x03);
      var s4 := PushN(s3, 2, 0x0400);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 2, 0x0240);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x0420);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x0260);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x0440);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 2, 0x0280);
      var s15 := MStore(s14);
      var s16 := PushN(s15, 1, 0x00);
      var s17 := PushN(s16, 2, 0x02a0);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 2, 0x032d);
      assert s19.stack[0] == 0x32d;
      var s20 := PushN(s19, 2, 0x0480);
      assert s20.stack[1] == 0x32d;
      var s21 := PushN(s20, 2, 0x1807);
      assert s21.stack[0] == 0x1807;
      assert s21.stack[2] == 0x32d;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s22, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 305
    * Starting at 0x1807
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1807 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x32d;
      var s2 := PushN(s1, 2, 0x0240);
      assert s2.stack[2] == 0x32d;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x32d;
      var s4 := PushN(s3, 2, 0x02c0);
      assert s4.stack[3] == 0x32d;
      var s5 := MStore(s4);
      assert s5.stack[1] == 0x32d;
      var s6 := PushN(s5, 2, 0x0260);
      assert s6.stack[2] == 0x32d;
      var s7 := MLoad(s6);
      assert s7.stack[2] == 0x32d;
      var s8 := PushN(s7, 2, 0x02e0);
      assert s8.stack[3] == 0x32d;
      var s9 := MStore(s8);
      assert s9.stack[1] == 0x32d;
      var s10 := PushN(s9, 2, 0x0280);
      assert s10.stack[2] == 0x32d;
      var s11 := MLoad(s10);
      assert s11.stack[2] == 0x32d;
      var s12 := PushN(s11, 2, 0x0300);
      assert s12.stack[3] == 0x32d;
      var s13 := MStore(s12);
      assert s13.stack[1] == 0x32d;
      var s14 := PushN(s13, 2, 0x02a0);
      assert s14.stack[2] == 0x32d;
      var s15 := MLoad(s14);
      assert s15.stack[2] == 0x32d;
      var s16 := IsZero(s15);
      assert s16.stack[2] == 0x32d;
      var s17 := PushN(s16, 2, 0x1867);
      assert s17.stack[0] == 0x1867;
      assert s17.stack[3] == 0x32d;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s119(s18, gas - 1)
      else
        ExecuteFromCFGNode_s107(s18, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 306
    * Starting at 0x1829
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1829 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x02c0);
      assert s1.stack[2] == 0x32d;
      var s2 := MLoad(s1);
      assert s2.stack[2] == 0x32d;
      var s3 := PushN(s2, 1, 0xe0);
      assert s3.stack[3] == 0x32d;
      var s4 := MStore(s3);
      assert s4.stack[1] == 0x32d;
      var s5 := PushN(s4, 2, 0x02e0);
      assert s5.stack[2] == 0x32d;
      var s6 := MLoad(s5);
      assert s6.stack[2] == 0x32d;
      var s7 := PushN(s6, 2, 0x0100);
      assert s7.stack[3] == 0x32d;
      var s8 := MStore(s7);
      assert s8.stack[1] == 0x32d;
      var s9 := PushN(s8, 2, 0x0300);
      assert s9.stack[2] == 0x32d;
      var s10 := MLoad(s9);
      assert s10.stack[2] == 0x32d;
      var s11 := PushN(s10, 2, 0x0120);
      assert s11.stack[3] == 0x32d;
      var s12 := MStore(s11);
      assert s12.stack[1] == 0x32d;
      var s13 := PushN(s12, 2, 0x184a);
      assert s13.stack[0] == 0x184a;
      assert s13.stack[2] == 0x32d;
      var s14 := PushN(s13, 2, 0x0320);
      assert s14.stack[1] == 0x184a;
      assert s14.stack[3] == 0x32d;
      var s15 := PushN(s14, 2, 0x16e6);
      assert s15.stack[0] == 0x16e6;
      assert s15.stack[2] == 0x184a;
      assert s15.stack[4] == 0x32d;
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s16, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 290
    * Starting at 0x16e6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x184a

    requires s0.stack[3] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x184a;
      assert s1.stack[3] == 0x32d;
      var s2 := PushN(s1, 1, 0xe0);
      assert s2.stack[2] == 0x184a;
      assert s2.stack[4] == 0x32d;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x184a;
      assert s3.stack[4] == 0x32d;
      var s4 := PushN(s3, 2, 0x0140);
      assert s4.stack[3] == 0x184a;
      assert s4.stack[5] == 0x32d;
      var s5 := MStore(s4);
      assert s5.stack[1] == 0x184a;
      assert s5.stack[3] == 0x32d;
      var s6 := PushN(s5, 2, 0x0100);
      assert s6.stack[2] == 0x184a;
      assert s6.stack[4] == 0x32d;
      var s7 := MLoad(s6);
      assert s7.stack[2] == 0x184a;
      assert s7.stack[4] == 0x32d;
      var s8 := PushN(s7, 2, 0x0160);
      assert s8.stack[3] == 0x184a;
      assert s8.stack[5] == 0x32d;
      var s9 := MStore(s8);
      assert s9.stack[1] == 0x184a;
      assert s9.stack[3] == 0x32d;
      var s10 := PushN(s9, 2, 0x0120);
      assert s10.stack[2] == 0x184a;
      assert s10.stack[4] == 0x32d;
      var s11 := MLoad(s10);
      assert s11.stack[2] == 0x184a;
      assert s11.stack[4] == 0x32d;
      var s12 := PushN(s11, 2, 0x0180);
      assert s12.stack[3] == 0x184a;
      assert s12.stack[5] == 0x32d;
      var s13 := MStore(s12);
      assert s13.stack[1] == 0x184a;
      assert s13.stack[3] == 0x32d;
      var s14 := PushN(s13, 2, 0x01a0);
      assert s14.stack[2] == 0x184a;
      assert s14.stack[4] == 0x32d;
      var s15 := PushN(s14, 1, 0x01);
      assert s15.stack[3] == 0x184a;
      assert s15.stack[5] == 0x32d;
      var s16 := PushN(s15, 1, 0x02);
      assert s16.stack[4] == 0x184a;
      assert s16.stack[6] == 0x32d;
      var s17 := Dup(s16, 2);
      assert s17.stack[5] == 0x184a;
      assert s17.stack[7] == 0x32d;
      var s18 := Dup(s17, 4);
      assert s18.stack[6] == 0x184a;
      assert s18.stack[8] == 0x32d;
      var s19 := MStore(s18);
      assert s19.stack[4] == 0x184a;
      assert s19.stack[6] == 0x32d;
      var s20 := Add(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s109(s20, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 291
    * Starting at 0x1709
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1709 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x184a

    requires s0.stack[5] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x184a;
      assert s1.stack[5] == 0x32d;
      var s2 := PushN(s1, 2, 0x0140);
      assert s2.stack[4] == 0x184a;
      assert s2.stack[6] == 0x32d;
      var s3 := PushN(s2, 2, 0x01a0);
      assert s3.stack[5] == 0x184a;
      assert s3.stack[7] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[5] == 0x184a;
      assert s4.stack[7] == 0x32d;
      var s5 := PushN(s4, 1, 0x03);
      assert s5.stack[6] == 0x184a;
      assert s5.stack[8] == 0x32d;
      var s6 := Dup(s5, 2);
      assert s6.stack[7] == 0x184a;
      assert s6.stack[9] == 0x32d;
      var s7 := Lt(s6);
      assert s7.stack[6] == 0x184a;
      assert s7.stack[8] == 0x32d;
      var s8 := IsZero(s7);
      assert s8.stack[6] == 0x184a;
      assert s8.stack[8] == 0x32d;
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      assert s9.stack[7] == 0x184a;
      assert s9.stack[9] == 0x32d;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s10, gas - 1)
      else
        ExecuteFromCFGNode_s110(s10, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 292
    * Starting at 0x171a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x171a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[6] == 0x184a;
      assert s1.stack[8] == 0x32d;
      var s2 := Mul(s1);
      assert s2.stack[5] == 0x184a;
      assert s2.stack[7] == 0x32d;
      var s3 := Add(s2);
      assert s3.stack[4] == 0x184a;
      assert s3.stack[6] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[4] == 0x184a;
      assert s4.stack[6] == 0x32d;
      var s5 := PushN(s4, 2, 0x01c0);
      assert s5.stack[5] == 0x184a;
      assert s5.stack[7] == 0x32d;
      var s6 := MStore(s5);
      assert s6.stack[3] == 0x184a;
      assert s6.stack[5] == 0x32d;
      var s7 := PushN(s6, 2, 0x01a0);
      assert s7.stack[4] == 0x184a;
      assert s7.stack[6] == 0x32d;
      var s8 := MLoad(s7);
      assert s8.stack[4] == 0x184a;
      assert s8.stack[6] == 0x32d;
      var s9 := PushN(s8, 2, 0x01e0);
      assert s9.stack[5] == 0x184a;
      assert s9.stack[7] == 0x32d;
      var s10 := MStore(s9);
      assert s10.stack[3] == 0x184a;
      assert s10.stack[5] == 0x32d;
      var s11 := PushN(s10, 2, 0x0200);
      assert s11.stack[4] == 0x184a;
      assert s11.stack[6] == 0x32d;
      var s12 := PushN(s11, 1, 0x00);
      assert s12.stack[5] == 0x184a;
      assert s12.stack[7] == 0x32d;
      var s13 := PushN(s12, 1, 0x03);
      assert s13.stack[6] == 0x184a;
      assert s13.stack[8] == 0x32d;
      var s14 := Dup(s13, 2);
      assert s14.stack[7] == 0x184a;
      assert s14.stack[9] == 0x32d;
      var s15 := Dup(s14, 4);
      assert s15.stack[8] == 0x184a;
      assert s15.stack[10] == 0x32d;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0x184a;
      assert s16.stack[8] == 0x32d;
      var s17 := Add(s16);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s111(s17, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 293
    * Starting at 0x1736
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1736 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x184a;
      assert s1.stack[7] == 0x32d;
      var s2 := PushN(s1, 2, 0x0140);
      assert s2.stack[6] == 0x184a;
      assert s2.stack[8] == 0x32d;
      var s3 := PushN(s2, 2, 0x01e0);
      assert s3.stack[7] == 0x184a;
      assert s3.stack[9] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[7] == 0x184a;
      assert s4.stack[9] == 0x32d;
      var s5 := PushN(s4, 1, 0x01);
      assert s5.stack[8] == 0x184a;
      assert s5.stack[10] == 0x32d;
      var s6 := Dup(s5, 1);
      assert s6.stack[9] == 0x184a;
      assert s6.stack[11] == 0x32d;
      var s7 := Dup(s6, 3);
      assert s7.stack[10] == 0x184a;
      assert s7.stack[12] == 0x32d;
      var s8 := Lt(s7);
      assert s8.stack[9] == 0x184a;
      assert s8.stack[11] == 0x32d;
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      assert s9.stack[10] == 0x184a;
      assert s9.stack[12] == 0x32d;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s10, gas - 1)
      else
        ExecuteFromCFGNode_s112(s10, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 294
    * Starting at 0x1747
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1747 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x184a

    requires s0.stack[10] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[9] == 0x184a;
      assert s1.stack[11] == 0x32d;
      var s2 := Dup(s1, 3);
      assert s2.stack[10] == 0x184a;
      assert s2.stack[12] == 0x32d;
      var s3 := Sub(s2);
      assert s3.stack[9] == 0x184a;
      assert s3.stack[11] == 0x32d;
      var s4 := Swap(s3, 1);
      assert s4.stack[9] == 0x184a;
      assert s4.stack[11] == 0x32d;
      var s5 := Pop(s4);
      assert s5.stack[8] == 0x184a;
      assert s5.stack[10] == 0x32d;
      var s6 := Swap(s5, 1);
      assert s6.stack[8] == 0x184a;
      assert s6.stack[10] == 0x32d;
      var s7 := Pop(s6);
      assert s7.stack[7] == 0x184a;
      assert s7.stack[9] == 0x32d;
      var s8 := PushN(s7, 1, 0x03);
      assert s8.stack[8] == 0x184a;
      assert s8.stack[10] == 0x32d;
      var s9 := Dup(s8, 2);
      assert s9.stack[9] == 0x184a;
      assert s9.stack[11] == 0x32d;
      var s10 := Lt(s9);
      assert s10.stack[8] == 0x184a;
      assert s10.stack[10] == 0x32d;
      var s11 := IsZero(s10);
      assert s11.stack[8] == 0x184a;
      assert s11.stack[10] == 0x32d;
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      assert s12.stack[9] == 0x184a;
      assert s12.stack[11] == 0x32d;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s200(s13, gas - 1)
      else
        ExecuteFromCFGNode_s113(s13, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 295
    * Starting at 0x1757
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1757 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x184a

    requires s0.stack[9] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[8] == 0x184a;
      assert s1.stack[10] == 0x32d;
      var s2 := Mul(s1);
      assert s2.stack[7] == 0x184a;
      assert s2.stack[9] == 0x32d;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x184a;
      assert s3.stack[8] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[6] == 0x184a;
      assert s4.stack[8] == 0x32d;
      var s5 := PushN(s4, 2, 0x0220);
      assert s5.stack[7] == 0x184a;
      assert s5.stack[9] == 0x32d;
      var s6 := MStore(s5);
      assert s6.stack[5] == 0x184a;
      assert s6.stack[7] == 0x32d;
      var s7 := PushN(s6, 2, 0x01c0);
      assert s7.stack[6] == 0x184a;
      assert s7.stack[8] == 0x32d;
      var s8 := MLoad(s7);
      assert s8.stack[6] == 0x184a;
      assert s8.stack[8] == 0x32d;
      var s9 := PushN(s8, 2, 0x0220);
      assert s9.stack[7] == 0x184a;
      assert s9.stack[9] == 0x32d;
      var s10 := MLoad(s9);
      assert s10.stack[7] == 0x184a;
      assert s10.stack[9] == 0x32d;
      var s11 := Gt(s10);
      assert s11.stack[6] == 0x184a;
      assert s11.stack[8] == 0x32d;
      var s12 := IsZero(s11);
      assert s12.stack[6] == 0x184a;
      assert s12.stack[8] == 0x32d;
      var s13 := PushN(s12, 2, 0x1772);
      assert s13.stack[0] == 0x1772;
      assert s13.stack[7] == 0x184a;
      assert s13.stack[9] == 0x32d;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s14, gas - 1)
      else
        ExecuteFromCFGNode_s114(s14, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 296
    * Starting at 0x176e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x176e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x17c0);
      assert s1.stack[0] == 0x17c0;
      assert s1.stack[6] == 0x184a;
      assert s1.stack[8] == 0x32d;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s2, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 302
    * Starting at 0x17c0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x184a;
      assert s1.stack[7] == 0x32d;
      var s2 := Pop(s1);
      assert s2.stack[4] == 0x184a;
      assert s2.stack[6] == 0x32d;
      var s3 := Pop(s2);
      assert s3.stack[3] == 0x184a;
      assert s3.stack[5] == 0x32d;
      var s4 := PushN(s3, 2, 0x01c0);
      assert s4.stack[4] == 0x184a;
      assert s4.stack[6] == 0x32d;
      var s5 := MLoad(s4);
      assert s5.stack[4] == 0x184a;
      assert s5.stack[6] == 0x32d;
      var s6 := PushN(s5, 2, 0x0140);
      assert s6.stack[5] == 0x184a;
      assert s6.stack[7] == 0x32d;
      var s7 := PushN(s6, 2, 0x01e0);
      assert s7.stack[6] == 0x184a;
      assert s7.stack[8] == 0x32d;
      var s8 := MLoad(s7);
      assert s8.stack[6] == 0x184a;
      assert s8.stack[8] == 0x32d;
      var s9 := PushN(s8, 1, 0x03);
      assert s9.stack[7] == 0x184a;
      assert s9.stack[9] == 0x32d;
      var s10 := Dup(s9, 2);
      assert s10.stack[8] == 0x184a;
      assert s10.stack[10] == 0x32d;
      var s11 := Lt(s10);
      assert s11.stack[7] == 0x184a;
      assert s11.stack[9] == 0x32d;
      var s12 := IsZero(s11);
      assert s12.stack[7] == 0x184a;
      assert s12.stack[9] == 0x32d;
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      assert s13.stack[8] == 0x184a;
      assert s13.stack[10] == 0x32d;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s14, gas - 1)
      else
        ExecuteFromCFGNode_s116(s14, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 303
    * Starting at 0x17d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x184a

    requires s0.stack[8] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[7] == 0x184a;
      assert s1.stack[9] == 0x32d;
      var s2 := Mul(s1);
      assert s2.stack[6] == 0x184a;
      assert s2.stack[8] == 0x32d;
      var s3 := Add(s2);
      assert s3.stack[5] == 0x184a;
      assert s3.stack[7] == 0x32d;
      var s4 := MStore(s3);
      assert s4.stack[3] == 0x184a;
      assert s4.stack[5] == 0x32d;
      var s5 := Dup(s4, 2);
      assert s5.stack[4] == 0x184a;
      assert s5.stack[6] == 0x32d;
      var s6 := MLoad(s5);
      assert s6.stack[4] == 0x184a;
      assert s6.stack[6] == 0x32d;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[5] == 0x184a;
      assert s7.stack[7] == 0x32d;
      var s8 := Add(s7);
      assert s8.stack[4] == 0x184a;
      assert s8.stack[6] == 0x32d;
      var s9 := Dup(s8, 1);
      assert s9.stack[5] == 0x184a;
      assert s9.stack[7] == 0x32d;
      var s10 := Dup(s9, 4);
      assert s10.stack[6] == 0x184a;
      assert s10.stack[8] == 0x32d;
      var s11 := MStore(s10);
      assert s11.stack[4] == 0x184a;
      assert s11.stack[6] == 0x32d;
      var s12 := Dup(s11, 2);
      assert s12.stack[5] == 0x184a;
      assert s12.stack[7] == 0x32d;
      var s13 := Eq(s12);
      assert s13.stack[4] == 0x184a;
      assert s13.stack[6] == 0x32d;
      var s14 := IsZero(s13);
      assert s14.stack[4] == 0x184a;
      assert s14.stack[6] == 0x32d;
      var s15 := PushN(s14, 2, 0x1709);
      assert s15.stack[0] == 0x1709;
      assert s15.stack[5] == 0x184a;
      assert s15.stack[7] == 0x32d;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s109(s16, gas - 1)
      else
        ExecuteFromCFGNode_s117(s16, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 304
    * Starting at 0x17eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x184a

    requires s0.stack[5] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0x184a;
      assert s1.stack[4] == 0x32d;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x184a;
      assert s2.stack[3] == 0x32d;
      var s3 := PushN(s2, 2, 0x0140);
      assert s3.stack[2] == 0x184a;
      assert s3.stack[4] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[2] == 0x184a;
      assert s4.stack[4] == 0x32d;
      var s5 := Dup(s4, 2);
      assert s5.stack[3] == 0x184a;
      assert s5.stack[5] == 0x32d;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0x184a;
      assert s6.stack[3] == 0x32d;
      var s7 := PushN(s6, 2, 0x0160);
      assert s7.stack[2] == 0x184a;
      assert s7.stack[4] == 0x32d;
      var s8 := MLoad(s7);
      assert s8.stack[2] == 0x184a;
      assert s8.stack[4] == 0x32d;
      var s9 := Dup(s8, 2);
      assert s9.stack[3] == 0x184a;
      assert s9.stack[5] == 0x32d;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[4] == 0x184a;
      assert s10.stack[6] == 0x32d;
      var s11 := Add(s10);
      assert s11.stack[3] == 0x184a;
      assert s11.stack[5] == 0x32d;
      var s12 := MStore(s11);
      assert s12.stack[1] == 0x184a;
      assert s12.stack[3] == 0x32d;
      var s13 := PushN(s12, 2, 0x0180);
      assert s13.stack[2] == 0x184a;
      assert s13.stack[4] == 0x32d;
      var s14 := MLoad(s13);
      assert s14.stack[2] == 0x184a;
      assert s14.stack[4] == 0x32d;
      var s15 := Dup(s14, 2);
      assert s15.stack[3] == 0x184a;
      assert s15.stack[5] == 0x32d;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[4] == 0x184a;
      assert s16.stack[6] == 0x32d;
      var s17 := Add(s16);
      assert s17.stack[3] == 0x184a;
      assert s17.stack[5] == 0x32d;
      var s18 := MStore(s17);
      assert s18.stack[1] == 0x184a;
      assert s18.stack[3] == 0x32d;
      var s19 := Pop(s18);
      assert s19.stack[0] == 0x184a;
      assert s19.stack[2] == 0x32d;
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s20, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 307
    * Starting at 0x184a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x184a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x32d;
      var s2 := PushN(s1, 2, 0x0320);
      assert s2.stack[2] == 0x32d;
      var s3 := Dup(s2, 1);
      assert s3.stack[3] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[3] == 0x32d;
      var s5 := PushN(s4, 2, 0x02c0);
      assert s5.stack[4] == 0x32d;
      var s6 := MStore(s5);
      assert s6.stack[2] == 0x32d;
      var s7 := Dup(s6, 1);
      assert s7.stack[3] == 0x32d;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[4] == 0x32d;
      var s9 := Add(s8);
      assert s9.stack[3] == 0x32d;
      var s10 := MLoad(s9);
      assert s10.stack[3] == 0x32d;
      var s11 := PushN(s10, 2, 0x02e0);
      assert s11.stack[4] == 0x32d;
      var s12 := MStore(s11);
      assert s12.stack[2] == 0x32d;
      var s13 := Dup(s12, 1);
      assert s13.stack[3] == 0x32d;
      var s14 := PushN(s13, 1, 0x40);
      assert s14.stack[4] == 0x32d;
      var s15 := Add(s14);
      assert s15.stack[3] == 0x32d;
      var s16 := MLoad(s15);
      assert s16.stack[3] == 0x32d;
      var s17 := PushN(s16, 2, 0x0300);
      assert s17.stack[4] == 0x32d;
      var s18 := MStore(s17);
      assert s18.stack[2] == 0x32d;
      var s19 := Pop(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s119(s19, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 308
    * Starting at 0x1867
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1867 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x32d;
      var s2 := PushN(s1, 2, 0x02c0);
      assert s2.stack[2] == 0x32d;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x32d;
      var s4 := PushN(s3, 2, 0x0320);
      assert s4.stack[3] == 0x32d;
      var s5 := MStore(s4);
      assert s5.stack[1] == 0x32d;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[2] == 0x32d;
      var s7 := PushN(s6, 2, 0x0340);
      assert s7.stack[3] == 0x32d;
      var s8 := MStore(s7);
      assert s8.stack[1] == 0x32d;
      var s9 := PushN(s8, 2, 0x0360);
      assert s9.stack[2] == 0x32d;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[3] == 0x32d;
      var s11 := PushN(s10, 1, 0xff);
      assert s11.stack[4] == 0x32d;
      var s12 := Dup(s11, 2);
      assert s12.stack[5] == 0x32d;
      var s13 := Dup(s12, 4);
      assert s13.stack[6] == 0x32d;
      var s14 := MStore(s13);
      assert s14.stack[4] == 0x32d;
      var s15 := Add(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s120(s15, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 309
    * Starting at 0x1881
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1881 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x32d;
      var s2 := PushN(s1, 2, 0x0320);
      assert s2.stack[4] == 0x32d;
      var s3 := MLoad(s2);
      assert s3.stack[4] == 0x32d;
      var s4 := PushN(s3, 2, 0x0380);
      assert s4.stack[5] == 0x32d;
      var s5 := MStore(s4);
      assert s5.stack[3] == 0x32d;
      var s6 := PushN(s5, 8, 0x0de0b6b3a7640000);
      assert s6.stack[4] == 0x32d;
      var s7 := PushN(s6, 2, 0x03a0);
      assert s7.stack[5] == 0x32d;
      var s8 := MStore(s7);
      assert s8.stack[3] == 0x32d;
      var s9 := PushN(s8, 2, 0x03e0);
      assert s9.stack[4] == 0x32d;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[5] == 0x32d;
      var s11 := PushN(s10, 1, 0x03);
      assert s11.stack[6] == 0x32d;
      var s12 := Dup(s11, 2);
      assert s12.stack[7] == 0x32d;
      var s13 := Dup(s12, 4);
      assert s13.stack[8] == 0x32d;
      var s14 := MStore(s13);
      assert s14.stack[6] == 0x32d;
      var s15 := Add(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s121(s15, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 310
    * Starting at 0x18a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x32d;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[6] == 0x32d;
      var s3 := PushN(s2, 2, 0x03e0);
      assert s3.stack[7] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[7] == 0x32d;
      var s5 := Mul(s4);
      assert s5.stack[6] == 0x32d;
      var s6 := PushN(s5, 2, 0x02c0);
      assert s6.stack[7] == 0x32d;
      var s7 := Add(s6);
      assert s7.stack[6] == 0x32d;
      var s8 := MLoad(s7);
      assert s8.stack[6] == 0x32d;
      var s9 := PushN(s8, 2, 0x03c0);
      assert s9.stack[7] == 0x32d;
      var s10 := MStore(s9);
      assert s10.stack[5] == 0x32d;
      var s11 := PushN(s10, 2, 0x03a0);
      assert s11.stack[6] == 0x32d;
      var s12 := MLoad(s11);
      assert s12.stack[6] == 0x32d;
      var s13 := PushN(s12, 2, 0x03c0);
      assert s13.stack[7] == 0x32d;
      var s14 := MLoad(s13);
      assert s14.stack[7] == 0x32d;
      var s15 := Dup(s14, 1);
      assert s15.stack[8] == 0x32d;
      var s16 := Dup(s15, 3);
      assert s16.stack[9] == 0x32d;
      var s17 := Mul(s16);
      assert s17.stack[8] == 0x32d;
      var s18 := Dup(s17, 3);
      assert s18.stack[9] == 0x32d;
      var s19 := IsZero(s18);
      assert s19.stack[9] == 0x32d;
      var s20 := Dup(s19, 3);
      assert s20.stack[10] == 0x32d;
      var s21 := Dup(s20, 5);
      assert s21.stack[11] == 0x32d;
      var s22 := Dup(s21, 4);
      assert s22.stack[12] == 0x32d;
      var s23 := Div(s22);
      assert s23.stack[11] == 0x32d;
      var s24 := Eq(s23);
      assert s24.stack[10] == 0x32d;
      var s25 := Or(s24);
      assert s25.stack[9] == 0x32d;
      var s26 := IsZero(s25);
      assert s26.stack[9] == 0x32d;
      var s27 := PushN(s26, 2, 0x1a5b);
      assert s27.stack[0] == 0x1a5b;
      assert s27.stack[10] == 0x32d;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s192(s28, gas - 1)
      else
        ExecuteFromCFGNode_s122(s28, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 311
    * Starting at 0x18cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[8] == 0x32d;
      var s2 := Pop(s1);
      assert s2.stack[7] == 0x32d;
      var s3 := Swap(s2, 1);
      assert s3.stack[7] == 0x32d;
      var s4 := Pop(s3);
      assert s4.stack[6] == 0x32d;
      var s5 := PushN(s4, 2, 0x0320);
      assert s5.stack[7] == 0x32d;
      var s6 := MLoad(s5);
      assert s6.stack[7] == 0x32d;
      var s7 := Dup(s6, 1);
      assert s7.stack[8] == 0x32d;
      var s8 := Dup(s7, 1);
      assert s8.stack[9] == 0x32d;
      var s9 := IsZero(s8);
      assert s9.stack[9] == 0x32d;
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      assert s10.stack[10] == 0x32d;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s192(s11, gas - 1)
      else
        ExecuteFromCFGNode_s123(s11, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 312
    * Starting at 0x18da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[9] == 0x32d;
      var s2 := Div(s1);
      assert s2.stack[8] == 0x32d;
      var s3 := Swap(s2, 1);
      assert s3.stack[8] == 0x32d;
      var s4 := Pop(s3);
      assert s4.stack[7] == 0x32d;
      var s5 := Swap(s4, 1);
      assert s5.stack[7] == 0x32d;
      var s6 := Pop(s5);
      assert s6.stack[6] == 0x32d;
      var s7 := PushN(s6, 2, 0x03a0);
      assert s7.stack[7] == 0x32d;
      var s8 := MStore(s7);
      assert s8.stack[5] == 0x32d;
      var s9 := Dup(s8, 2);
      assert s9.stack[6] == 0x32d;
      var s10 := MLoad(s9);
      assert s10.stack[6] == 0x32d;
      var s11 := PushN(s10, 1, 0x01);
      assert s11.stack[7] == 0x32d;
      var s12 := Add(s11);
      assert s12.stack[6] == 0x32d;
      var s13 := Dup(s12, 1);
      assert s13.stack[7] == 0x32d;
      var s14 := Dup(s13, 4);
      assert s14.stack[8] == 0x32d;
      var s15 := MStore(s14);
      assert s15.stack[6] == 0x32d;
      var s16 := Dup(s15, 2);
      assert s16.stack[7] == 0x32d;
      var s17 := Eq(s16);
      assert s17.stack[6] == 0x32d;
      var s18 := IsZero(s17);
      assert s18.stack[6] == 0x32d;
      var s19 := PushN(s18, 2, 0x18a2);
      assert s19.stack[0] == 0x18a2;
      assert s19.stack[7] == 0x32d;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s20, gas - 1)
      else
        ExecuteFromCFGNode_s124(s20, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 313
    * Starting at 0x18f3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[4] == 0x32d;
      var s2 := Pop(s1);
      assert s2.stack[3] == 0x32d;
      var s3 := PushN(s2, 2, 0x0320);
      assert s3.stack[4] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[4] == 0x32d;
      var s5 := PushN(s4, 8, 0x1bc16d674ec80000);
      assert s5.stack[5] == 0x32d;
      var s6 := PushN(s5, 2, 0x03a0);
      assert s6.stack[6] == 0x32d;
      var s7 := MLoad(s6);
      assert s7.stack[6] == 0x32d;
      var s8 := Dup(s7, 2);
      assert s8.stack[7] == 0x32d;
      var s9 := Dup(s8, 2);
      assert s9.stack[8] == 0x32d;
      var s10 := Dup(s9, 4);
      assert s10.stack[9] == 0x32d;
      var s11 := Add(s10);
      assert s11.stack[8] == 0x32d;
      var s12 := Lt(s11);
      assert s12.stack[7] == 0x32d;
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      assert s13.stack[8] == 0x32d;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s14, gas - 1)
      else
        ExecuteFromCFGNode_s125(s14, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 314
    * Starting at 0x190f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x190f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[7] == 0x32d;
      var s2 := Dup(s1, 3);
      assert s2.stack[8] == 0x32d;
      var s3 := Add(s2);
      assert s3.stack[7] == 0x32d;
      var s4 := Swap(s3, 1);
      assert s4.stack[7] == 0x32d;
      var s5 := Pop(s4);
      assert s5.stack[6] == 0x32d;
      var s6 := Swap(s5, 1);
      assert s6.stack[6] == 0x32d;
      var s7 := Pop(s6);
      assert s7.stack[5] == 0x32d;
      var s8 := Dup(s7, 1);
      assert s8.stack[6] == 0x32d;
      var s9 := Dup(s8, 3);
      assert s9.stack[7] == 0x32d;
      var s10 := Mul(s9);
      assert s10.stack[6] == 0x32d;
      var s11 := Dup(s10, 3);
      assert s11.stack[7] == 0x32d;
      var s12 := IsZero(s11);
      assert s12.stack[7] == 0x32d;
      var s13 := Dup(s12, 3);
      assert s13.stack[8] == 0x32d;
      var s14 := Dup(s13, 5);
      assert s14.stack[9] == 0x32d;
      var s15 := Dup(s14, 4);
      assert s15.stack[10] == 0x32d;
      var s16 := Div(s15);
      assert s16.stack[9] == 0x32d;
      var s17 := Eq(s16);
      assert s17.stack[8] == 0x32d;
      var s18 := Or(s17);
      assert s18.stack[7] == 0x32d;
      var s19 := IsZero(s18);
      assert s19.stack[7] == 0x32d;
      var s20 := PushN(s19, 2, 0x1a5b);
      assert s20.stack[0] == 0x1a5b;
      assert s20.stack[8] == 0x32d;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s21, gas - 1)
      else
        ExecuteFromCFGNode_s126(s21, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 315
    * Starting at 0x1926
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1926 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[6] == 0x32d;
      var s2 := Pop(s1);
      assert s2.stack[5] == 0x32d;
      var s3 := Swap(s2, 1);
      assert s3.stack[5] == 0x32d;
      var s4 := Pop(s3);
      assert s4.stack[4] == 0x32d;
      var s5 := PushN(s4, 8, 0x29a2241af62c0000);
      assert s5.stack[5] == 0x32d;
      var s6 := Dup(s5, 1);
      assert s6.stack[6] == 0x32d;
      var s7 := Dup(s6, 3);
      assert s7.stack[7] == 0x32d;
      var s8 := Div(s7);
      assert s8.stack[6] == 0x32d;
      var s9 := Swap(s8, 1);
      assert s9.stack[6] == 0x32d;
      var s10 := Pop(s9);
      assert s10.stack[5] == 0x32d;
      var s11 := Swap(s10, 1);
      assert s11.stack[5] == 0x32d;
      var s12 := Pop(s11);
      assert s12.stack[4] == 0x32d;
      var s13 := PushN(s12, 2, 0x0320);
      assert s13.stack[5] == 0x32d;
      var s14 := MStore(s13);
      assert s14.stack[3] == 0x32d;
      var s15 := PushN(s14, 2, 0x0380);
      assert s15.stack[4] == 0x32d;
      var s16 := MLoad(s15);
      assert s16.stack[4] == 0x32d;
      var s17 := PushN(s16, 2, 0x0320);
      assert s17.stack[5] == 0x32d;
      var s18 := MLoad(s17);
      assert s18.stack[5] == 0x32d;
      var s19 := Gt(s18);
      assert s19.stack[4] == 0x32d;
      var s20 := PushN(s19, 2, 0x1969);
      assert s20.stack[0] == 0x1969;
      assert s20.stack[5] == 0x32d;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s21, gas - 1)
      else
        ExecuteFromCFGNode_s127(s21, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 316
    * Starting at 0x194b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x194b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0380);
      assert s1.stack[4] == 0x32d;
      var s2 := MLoad(s1);
      assert s2.stack[4] == 0x32d;
      var s3 := PushN(s2, 2, 0x0320);
      assert s3.stack[5] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[5] == 0x32d;
      var s5 := Dup(s4, 1);
      assert s5.stack[6] == 0x32d;
      var s6 := Dup(s5, 3);
      assert s6.stack[7] == 0x32d;
      var s7 := Lt(s6);
      assert s7.stack[6] == 0x32d;
      var s8 := PushN(s7, 2, 0x1a5b);
      assert s8.stack[0] == 0x1a5b;
      assert s8.stack[7] == 0x32d;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s9, gas - 1)
      else
        ExecuteFromCFGNode_s128(s9, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 317
    * Starting at 0x195a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x195a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[6] == 0x32d;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0x32d;
      var s3 := Sub(s2);
      assert s3.stack[6] == 0x32d;
      var s4 := Swap(s3, 1);
      assert s4.stack[6] == 0x32d;
      var s5 := Pop(s4);
      assert s5.stack[5] == 0x32d;
      var s6 := Swap(s5, 1);
      assert s6.stack[5] == 0x32d;
      var s7 := Pop(s6);
      assert s7.stack[4] == 0x32d;
      var s8 := PushN(s7, 2, 0x0340);
      assert s8.stack[5] == 0x32d;
      var s9 := MStore(s8);
      assert s9.stack[3] == 0x32d;
      var s10 := PushN(s9, 2, 0x1984);
      assert s10.stack[0] == 0x1984;
      assert s10.stack[4] == 0x32d;
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s11, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 320
    * Starting at 0x1984
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1984 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x32d;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[4] == 0x32d;
      var s3 := PushN(s2, 2, 0x0340);
      assert s3.stack[5] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[5] == 0x32d;
      var s5 := Gt(s4);
      assert s5.stack[4] == 0x32d;
      var s6 := IsZero(s5);
      assert s6.stack[4] == 0x32d;
      var s7 := PushN(s6, 2, 0x19bb);
      assert s7.stack[0] == 0x19bb;
      assert s7.stack[5] == 0x32d;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s187(s8, gas - 1)
      else
        ExecuteFromCFGNode_s130(s8, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 321
    * Starting at 0x1991
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1991 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0320);
      assert s1.stack[4] == 0x32d;
      var s2 := MLoad(s1);
      assert s2.stack[4] == 0x32d;
      var s3 := PushN(s2, 2, 0x0340);
      assert s3.stack[5] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[5] == 0x32d;
      var s5 := PushN(s4, 8, 0x0de0b6b3a7640000);
      assert s5.stack[6] == 0x32d;
      var s6 := Dup(s5, 1);
      assert s6.stack[7] == 0x32d;
      var s7 := Dup(s6, 3);
      assert s7.stack[8] == 0x32d;
      var s8 := Mul(s7);
      assert s8.stack[7] == 0x32d;
      var s9 := Dup(s8, 3);
      assert s9.stack[8] == 0x32d;
      var s10 := IsZero(s9);
      assert s10.stack[8] == 0x32d;
      var s11 := Dup(s10, 3);
      assert s11.stack[9] == 0x32d;
      var s12 := Dup(s11, 5);
      assert s12.stack[10] == 0x32d;
      var s13 := Dup(s12, 4);
      assert s13.stack[11] == 0x32d;
      var s14 := Div(s13);
      assert s14.stack[10] == 0x32d;
      var s15 := Eq(s14);
      assert s15.stack[9] == 0x32d;
      var s16 := Or(s15);
      assert s16.stack[8] == 0x32d;
      var s17 := IsZero(s16);
      assert s17.stack[8] == 0x32d;
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      assert s18.stack[9] == 0x32d;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s19, gas - 1)
      else
        ExecuteFromCFGNode_s131(s19, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 322
    * Starting at 0x19b2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[7] == 0x32d;
      var s2 := Pop(s1);
      assert s2.stack[6] == 0x32d;
      var s3 := Swap(s2, 1);
      assert s3.stack[6] == 0x32d;
      var s4 := Pop(s3);
      assert s4.stack[5] == 0x32d;
      var s5 := Lt(s4);
      assert s5.stack[4] == 0x32d;
      var s6 := PushN(s5, 2, 0x19be);
      assert s6.stack[0] == 0x19be;
      assert s6.stack[5] == 0x32d;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s7, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 324
    * Starting at 0x19be
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x32d;
      var s2 := IsZero(s1);
      assert s2.stack[4] == 0x32d;
      var s3 := PushN(s2, 2, 0x19d1);
      assert s3.stack[0] == 0x19d1;
      assert s3.stack[5] == 0x32d;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s4, gas - 1)
      else
        ExecuteFromCFGNode_s133(s4, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 325
    * Starting at 0x19c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0x32d;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x32d;
      var s3 := PushN(s2, 2, 0x0320);
      assert s3.stack[2] == 0x32d;
      var s4 := MLoad(s3);
      assert s4.stack[2] == 0x32d;
      var s5 := Dup(s4, 2);
      assert s5.stack[3] == 0x32d;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0x32d;
      var s7 := Pop(s6);
      assert s7.stack[0] == 0x32d;
      var s8 := PushN(s7, 2, 0x1a59);
      assert s8.stack[0] == 0x1a59;
      assert s8.stack[1] == 0x32d;
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s9, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 329
    * Starting at 0x1a59
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0x32d;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s2, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 47
    * Starting at 0x32d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0480);
      var s3 := MLoad(s2);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := Mul(s5);
      var s7 := Dup(s6, 3);
      var s8 := IsZero(s7);
      var s9 := Dup(s8, 3);
      var s10 := Dup(s9, 5);
      var s11 := Dup(s10, 4);
      var s12 := Div(s11);
      var s13 := Eq(s12);
      var s14 := Or(s13);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x1a5b);
      assert s16.stack[0] == 0x1a5b;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s17, gas - 1)
      else
        ExecuteFromCFGNode_s136(s17, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 48
    * Starting at 0x342
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0460);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 2, 0x0480);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x04c0);
      var s11 := PushN(s10, 1, 0x00);
      var s12 := PushN(s11, 1, 0x03);
      var s13 := Dup(s12, 2);
      var s14 := Dup(s13, 4);
      var s15 := MStore(s14);
      var s16 := Add(s15);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s137(s16, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 49
    * Starting at 0x35b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x04c0);
      var s4 := MLoad(s3);
      var s5 := Mul(s4);
      var s6 := PushN(s5, 2, 0x0400);
      var s7 := Add(s6);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x04a0);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x0480);
      var s12 := Dup(s11, 1);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 2, 0x04a0);
      var s15 := MLoad(s14);
      var s16 := Dup(s15, 2);
      var s17 := Dup(s16, 2);
      var s18 := Dup(s17, 4);
      var s19 := Add(s18);
      var s20 := Lt(s19);
      var s21 := PushN(s20, 2, 0x1a5b);
      assert s21.stack[0] == 0x1a5b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s22, gas - 1)
      else
        ExecuteFromCFGNode_s138(s22, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 50
    * Starting at 0x37e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := Dup(s7, 2);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      var s11 := Dup(s10, 2);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 1, 0x01);
      var s14 := Add(s13);
      var s15 := Dup(s14, 1);
      var s16 := Dup(s15, 4);
      var s17 := MStore(s16);
      var s18 := Dup(s17, 2);
      var s19 := Eq(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x035b);
      assert s21.stack[0] == 0x35b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s22, gas - 1)
      else
        ExecuteFromCFGNode_s139(s22, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 51
    * Starting at 0x397
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x397 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x04a0);
      var s4 := PushN(s3, 1, 0x00);
      var s5 := PushN(s4, 1, 0xff);
      var s6 := Dup(s5, 2);
      var s7 := Dup(s6, 4);
      var s8 := MStore(s7);
      var s9 := Add(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s140(s9, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 52
    * Starting at 0x3a4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0460);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x04c0);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 8, 0x0de0b6b3a7640000);
      var s7 := PushN(s6, 2, 0x04e0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0520);
      var s10 := PushN(s9, 1, 0x00);
      var s11 := PushN(s10, 1, 0x03);
      var s12 := Dup(s11, 2);
      var s13 := Dup(s12, 4);
      var s14 := MStore(s13);
      var s15 := Add(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s141(s15, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 53
    * Starting at 0x3c5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x20);
      var s3 := PushN(s2, 2, 0x0520);
      var s4 := MLoad(s3);
      var s5 := Mul(s4);
      var s6 := PushN(s5, 2, 0x0400);
      var s7 := Add(s6);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x0500);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 2, 0x04e0);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x0500);
      var s14 := MLoad(s13);
      var s15 := Dup(s14, 1);
      var s16 := Dup(s15, 3);
      var s17 := Mul(s16);
      var s18 := Dup(s17, 3);
      var s19 := IsZero(s18);
      var s20 := Dup(s19, 3);
      var s21 := Dup(s20, 5);
      var s22 := Dup(s21, 4);
      var s23 := Div(s22);
      var s24 := Eq(s23);
      var s25 := Or(s24);
      var s26 := IsZero(s25);
      var s27 := PushN(s26, 2, 0x1a5b);
      assert s27.stack[0] == 0x1a5b;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s28, gas - 1)
      else
        ExecuteFromCFGNode_s142(s28, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 54
    * Starting at 0x3ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x03);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Mul(s7);
      var s9 := Dup(s8, 3);
      var s10 := IsZero(s9);
      var s11 := Dup(s10, 3);
      var s12 := Dup(s11, 5);
      var s13 := Dup(s12, 4);
      var s14 := Div(s13);
      var s15 := Eq(s14);
      var s16 := Or(s15);
      var s17 := IsZero(s16);
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s19, gas - 1)
      else
        ExecuteFromCFGNode_s143(s19, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 55
    * Starting at 0x404
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x404 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0460);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s11, gas - 1)
      else
        ExecuteFromCFGNode_s144(s11, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 56
    * Starting at 0x413
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x413 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x04e0);
      var s8 := MStore(s7);
      var s9 := Dup(s8, 2);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 1, 0x01);
      var s12 := Add(s11);
      var s13 := Dup(s12, 1);
      var s14 := Dup(s13, 4);
      var s15 := MStore(s14);
      var s16 := Dup(s15, 2);
      var s17 := Eq(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x03c5);
      assert s19.stack[0] == 0x3c5;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s20, gas - 1)
      else
        ExecuteFromCFGNode_s145(s20, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 57
    * Starting at 0x42c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x24);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 8, 0x0de0b6b3a7640000);
      var s6 := Dup(s5, 2);
      var s7 := Dup(s6, 2);
      var s8 := Dup(s7, 4);
      var s9 := Add(s8);
      var s10 := Lt(s9);
      var s11 := PushN(s10, 2, 0x1a5b);
      assert s11.stack[0] == 0x1a5b;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s12, gas - 1)
      else
        ExecuteFromCFGNode_s146(s12, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 58
    * Starting at 0x443
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x443 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0500);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x04e0);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 2, 0x0500);
      var s13 := MLoad(s12);
      var s14 := Gt(s13);
      var s15 := PushN(s14, 2, 0x048b);
      assert s15.stack[0] == 0x48b;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s179(s16, gas - 1)
      else
        ExecuteFromCFGNode_s147(s16, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 59
    * Starting at 0x45b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x04e0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0500);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Lt(s6);
      var s8 := PushN(s7, 2, 0x1a5b);
      assert s8.stack[0] == 0x1a5b;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s9, gas - 1)
      else
        ExecuteFromCFGNode_s148(s9, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 60
    * Starting at 0x46a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s8 := PushN(s7, 1, 0x01);
      var s9 := Dup(s8, 2);
      var s10 := Dup(s9, 2);
      var s11 := Dup(s10, 4);
      var s12 := Add(s11);
      var s13 := Lt(s12);
      var s14 := PushN(s13, 2, 0x1a5b);
      assert s14.stack[0] == 0x1a5b;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s15, gas - 1)
      else
        ExecuteFromCFGNode_s149(s15, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 61
    * Starting at 0x47c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0500);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x04b8);
      assert s10.stack[0] == 0x4b8;
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s11, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 65
    * Starting at 0x4b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 8, 0x0de0b6b3a7640000);
      var s3 := PushN(s2, 2, 0x0460);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Mul(s6);
      var s8 := Dup(s7, 3);
      var s9 := IsZero(s8);
      var s10 := Dup(s9, 3);
      var s11 := Dup(s10, 5);
      var s12 := Dup(s11, 4);
      var s13 := Div(s12);
      var s14 := Eq(s13);
      var s15 := Or(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x1a5b);
      assert s17.stack[0] == 0x1a5b;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s18, gas - 1)
      else
        ExecuteFromCFGNode_s151(s18, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 66
    * Starting at 0x4d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x24);
      var s6 := CallDataLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s152(s11, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 67
    * Starting at 0x4e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0500);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := Dup(s9, 3);
      var s11 := Mul(s10);
      var s12 := Dup(s11, 3);
      var s13 := IsZero(s12);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := Dup(s15, 4);
      var s17 := Div(s16);
      var s18 := Eq(s17);
      var s19 := Or(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x1a5b);
      assert s21.stack[0] == 0x1a5b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s22, gas - 1)
      else
        ExecuteFromCFGNode_s153(s22, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 68
    * Starting at 0x4fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x24);
      var s6 := CallDataLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s154(s11, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 69
    * Starting at 0x50c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0500);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := Dup(s9, 3);
      var s11 := Mul(s10);
      var s12 := Dup(s11, 3);
      var s13 := IsZero(s12);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := Dup(s15, 4);
      var s17 := Div(s16);
      var s18 := Eq(s17);
      var s19 := Or(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x1a5b);
      assert s21.stack[0] == 0x1a5b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s22, gas - 1)
      else
        ExecuteFromCFGNode_s155(s22, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 70
    * Starting at 0x526
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x526 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x2710);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Mul(s7);
      var s9 := Dup(s8, 3);
      var s10 := IsZero(s9);
      var s11 := Dup(s10, 3);
      var s12 := Dup(s11, 5);
      var s13 := Dup(s12, 4);
      var s14 := Div(s13);
      var s15 := Eq(s14);
      var s16 := Or(s15);
      var s17 := IsZero(s16);
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s19, gas - 1)
      else
        ExecuteFromCFGNode_s156(s19, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 71
    * Starting at 0x53d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x04);
      var s6 := CallDataLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s157(s11, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 72
    * Starting at 0x54b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0520);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 8, 0x53444835ec580000);
      var s10 := PushN(s9, 2, 0x04e0);
      var s11 := MLoad(s10);
      var s12 := Dup(s11, 1);
      var s13 := Dup(s12, 3);
      var s14 := Mul(s13);
      var s15 := Dup(s14, 3);
      var s16 := IsZero(s15);
      var s17 := Dup(s16, 3);
      var s18 := Dup(s17, 5);
      var s19 := Dup(s18, 4);
      var s20 := Div(s19);
      var s21 := Eq(s20);
      var s22 := Or(s21);
      var s23 := IsZero(s22);
      var s24 := PushN(s23, 2, 0x1a5b);
      assert s24.stack[0] == 0x1a5b;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s25, gas - 1)
      else
        ExecuteFromCFGNode_s158(s25, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 73
    * Starting at 0x572
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x572 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0500);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s159(s11, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 74
    * Starting at 0x581
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x581 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0540);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0480);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x0480);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x0540);
      var s14 := MLoad(s13);
      var s15 := Dup(s14, 1);
      var s16 := Dup(s15, 3);
      var s17 := Mul(s16);
      var s18 := Dup(s17, 3);
      var s19 := IsZero(s18);
      var s20 := Dup(s19, 3);
      var s21 := Dup(s20, 5);
      var s22 := Dup(s21, 4);
      var s23 := Div(s22);
      var s24 := Eq(s23);
      var s25 := Or(s24);
      var s26 := IsZero(s25);
      var s27 := PushN(s26, 2, 0x1a5b);
      assert s27.stack[0] == 0x1a5b;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s28, gas - 1)
      else
        ExecuteFromCFGNode_s160(s28, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 75
    * Starting at 0x5a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 8, 0x0de0b6b3a7640000);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Div(s7);
      var s9 := Swap(s8, 1);
      var s10 := Pop(s9);
      var s11 := Swap(s10, 1);
      var s12 := Pop(s11);
      var s13 := Dup(s12, 2);
      var s14 := Dup(s13, 2);
      var s15 := Dup(s14, 4);
      var s16 := Add(s15);
      var s17 := Lt(s16);
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s19, gas - 1)
      else
        ExecuteFromCFGNode_s161(s19, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 76
    * Starting at 0x5c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0520);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x03);
      var s11 := Dup(s10, 1);
      var s12 := Dup(s11, 3);
      var s13 := Mul(s12);
      var s14 := Dup(s13, 3);
      var s15 := IsZero(s14);
      var s16 := Dup(s15, 3);
      var s17 := Dup(s16, 5);
      var s18 := Dup(s17, 4);
      var s19 := Div(s18);
      var s20 := Eq(s19);
      var s21 := Or(s20);
      var s22 := IsZero(s21);
      var s23 := PushN(s22, 2, 0x1a5b);
      assert s23.stack[0] == 0x1a5b;
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s24, gas - 1)
      else
        ExecuteFromCFGNode_s162(s24, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 77
    * Starting at 0x5e1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x04e0);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s11, gas - 1)
      else
        ExecuteFromCFGNode_s163(s11, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 78
    * Starting at 0x5f0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := Dup(s6, 2);
      var s8 := Dup(s7, 2);
      var s9 := Dup(s8, 4);
      var s10 := Add(s9);
      var s11 := Lt(s10);
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s13, gas - 1)
      else
        ExecuteFromCFGNode_s164(s13, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 79
    * Starting at 0x5ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0540);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x0460);
      var s11 := MLoad(s10);
      var s12 := Dup(s11, 1);
      var s13 := Dup(s12, 3);
      var s14 := Mul(s13);
      var s15 := Dup(s14, 3);
      var s16 := IsZero(s15);
      var s17 := Dup(s16, 3);
      var s18 := Dup(s17, 5);
      var s19 := Dup(s18, 4);
      var s20 := Div(s19);
      var s21 := Eq(s20);
      var s22 := Or(s21);
      var s23 := IsZero(s22);
      var s24 := PushN(s23, 2, 0x1a5b);
      assert s24.stack[0] == 0x1a5b;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s25, gas - 1)
      else
        ExecuteFromCFGNode_s165(s25, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 80
    * Starting at 0x61e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 8, 0x0de0b6b3a7640000);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Div(s7);
      var s9 := Swap(s8, 1);
      var s10 := Pop(s9);
      var s11 := Swap(s10, 1);
      var s12 := Pop(s11);
      var s13 := Dup(s12, 1);
      var s14 := Dup(s13, 3);
      var s15 := Lt(s14);
      var s16 := PushN(s15, 2, 0x1a5b);
      assert s16.stack[0] == 0x1a5b;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s17, gas - 1)
      else
        ExecuteFromCFGNode_s166(s17, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 81
    * Starting at 0x639
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x639 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s8 := PushN(s7, 2, 0x0560);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x0460);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 2, 0x0560);
      var s13 := MLoad(s12);
      var s14 := PushN(s13, 2, 0x0480);
      var s15 := MLoad(s14);
      var s16 := Dup(s15, 2);
      var s17 := Dup(s16, 2);
      var s18 := Dup(s17, 4);
      var s19 := Add(s18);
      var s20 := Lt(s19);
      var s21 := PushN(s20, 2, 0x1a5b);
      assert s21.stack[0] == 0x1a5b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s22, gas - 1)
      else
        ExecuteFromCFGNode_s167(s22, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 82
    * Starting at 0x659
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x659 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := Dup(s7, 1);
      var s9 := Dup(s8, 3);
      var s10 := Mul(s9);
      var s11 := Dup(s10, 3);
      var s12 := IsZero(s11);
      var s13 := Dup(s12, 3);
      var s14 := Dup(s13, 5);
      var s15 := Dup(s14, 4);
      var s16 := Div(s15);
      var s17 := Eq(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := PushN(s19, 2, 0x1a5b);
      assert s20.stack[0] == 0x1a5b;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s21, gas - 1)
      else
        ExecuteFromCFGNode_s168(s21, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 83
    * Starting at 0x670
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x670 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0560);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s169(s11, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 84
    * Starting at 0x67f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0580);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0460);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x0460);
      var s12 := MLoad(s11);
      var s13 := Dup(s12, 1);
      var s14 := Dup(s13, 3);
      var s15 := Mul(s14);
      var s16 := Dup(s15, 3);
      var s17 := IsZero(s16);
      var s18 := Dup(s17, 3);
      var s19 := Dup(s18, 5);
      var s20 := Dup(s19, 4);
      var s21 := Div(s20);
      var s22 := Eq(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := PushN(s24, 2, 0x1a5b);
      assert s25.stack[0] == 0x1a5b;
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s26, gas - 1)
      else
        ExecuteFromCFGNode_s170(s26, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 85
    * Starting at 0x6a1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0560);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s171(s11, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 86
    * Starting at 0x6b0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x05a0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x04e0);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 8, 0x0de0b6b3a7640000);
      var s12 := Gt(s11);
      var s13 := PushN(s12, 2, 0x0763);
      assert s13.stack[0] == 0x763;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s14, gas - 1)
      else
        ExecuteFromCFGNode_s172(s14, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 87
    * Starting at 0x6cc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x05a0);
      var s2 := Dup(s1, 1);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0460);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 2, 0x0520);
      var s7 := MLoad(s6);
      var s8 := PushN(s7, 2, 0x0560);
      var s9 := MLoad(s8);
      var s10 := Dup(s9, 1);
      var s11 := Dup(s10, 1);
      var s12 := IsZero(s11);
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s14, gas - 1)
      else
        ExecuteFromCFGNode_s173(s14, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 88
    * Starting at 0x6e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 3);
      var s9 := Mul(s8);
      var s10 := Dup(s9, 3);
      var s11 := IsZero(s10);
      var s12 := Dup(s11, 3);
      var s13 := Dup(s12, 5);
      var s14 := Dup(s13, 4);
      var s15 := Div(s14);
      var s16 := Eq(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x1a5b);
      assert s19.stack[0] == 0x1a5b;
      var s20 := JumpI(s19);
      // Segment is terminal (Revert, Stop or Return)
      s20
  }

  /** Node 174
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
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

  /** Node 175
    * Segment Id for this node is: 94
    * Starting at 0x763
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x763 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x05a0);
      var s3 := Dup(s2, 1);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0460);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0520);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x0560);
      var s10 := MLoad(s9);
      var s11 := Dup(s10, 1);
      var s12 := Dup(s11, 1);
      var s13 := IsZero(s12);
      var s14 := PushN(s13, 2, 0x1a5b);
      assert s14.stack[0] == 0x1a5b;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s15, gas - 1)
      else
        ExecuteFromCFGNode_s176(s15, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 95
    * Starting at 0x77c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 3);
      var s9 := Mul(s8);
      var s10 := Dup(s9, 3);
      var s11 := IsZero(s10);
      var s12 := Dup(s11, 3);
      var s13 := Dup(s12, 5);
      var s14 := Dup(s13, 4);
      var s15 := Div(s14);
      var s16 := Eq(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x1a5b);
      assert s19.stack[0] == 0x1a5b;
      var s20 := JumpI(s19);
      // Segment is terminal (Revert, Stop or Return)
      s20
  }

  /** Node 177
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
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

  /** Node 178
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
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

  /** Node 179
    * Segment Id for this node is: 62
    * Starting at 0x48b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0500);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x04e0);
      var s5 := MLoad(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Lt(s7);
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s10, gas - 1)
      else
        ExecuteFromCFGNode_s180(s10, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 63
    * Starting at 0x49b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s8 := PushN(s7, 1, 0x01);
      var s9 := Dup(s8, 2);
      var s10 := Dup(s9, 2);
      var s11 := Dup(s10, 4);
      var s12 := Add(s11);
      var s13 := Lt(s12);
      var s14 := PushN(s13, 2, 0x1a5b);
      assert s14.stack[0] == 0x1a5b;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s15, gas - 1)
      else
        ExecuteFromCFGNode_s181(s15, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 64
    * Starting at 0x4ad
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0500);
      var s9 := MStore(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s150(s9, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
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

  /** Node 183
    * Segment Id for this node is: 326
    * Starting at 0x19d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x32d;
      var s2 := Dup(s1, 2);
      assert s2.stack[4] == 0x32d;
      var s3 := MLoad(s2);
      assert s3.stack[4] == 0x32d;
      var s4 := PushN(s3, 1, 0x01);
      assert s4.stack[5] == 0x32d;
      var s5 := Add(s4);
      assert s5.stack[4] == 0x32d;
      var s6 := Dup(s5, 1);
      assert s6.stack[5] == 0x32d;
      var s7 := Dup(s6, 4);
      assert s7.stack[6] == 0x32d;
      var s8 := MStore(s7);
      assert s8.stack[4] == 0x32d;
      var s9 := Dup(s8, 2);
      assert s9.stack[5] == 0x32d;
      var s10 := Eq(s9);
      assert s10.stack[4] == 0x32d;
      var s11 := IsZero(s10);
      assert s11.stack[4] == 0x32d;
      var s12 := PushN(s11, 2, 0x1881);
      assert s12.stack[0] == 0x1881;
      assert s12.stack[5] == 0x32d;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s120(s13, gas - 1)
      else
        ExecuteFromCFGNode_s184(s13, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 327
    * Starting at 0x19e1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0x32d;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x32d;
      var s3 := PushN(s2, 1, 0x10);
      assert s3.stack[2] == 0x32d;
      var s4 := PushN(s3, 2, 0x0360);
      assert s4.stack[3] == 0x32d;
      var s5 := MStore(s4);
      assert s5.stack[1] == 0x32d;
      var s6 := PushN(s5, 32, 0x446964206e6f7420636f6e766572676500000000000000000000000000000000);
      assert s6.stack[2] == 0x32d;
      var s7 := PushN(s6, 2, 0x0380);
      assert s7.stack[3] == 0x32d;
      var s8 := MStore(s7);
      assert s8.stack[1] == 0x32d;
      var s9 := PushN(s8, 2, 0x0360);
      assert s9.stack[2] == 0x32d;
      var s10 := Pop(s9);
      assert s10.stack[1] == 0x32d;
      var s11 := PushN(s10, 2, 0x0360);
      assert s11.stack[2] == 0x32d;
      var s12 := MLoad(s11);
      assert s12.stack[2] == 0x32d;
      var s13 := Dup(s12, 1);
      assert s13.stack[3] == 0x32d;
      var s14 := PushN(s13, 2, 0x0380);
      assert s14.stack[4] == 0x32d;
      var s15 := Add(s14);
      assert s15.stack[3] == 0x32d;
      var s16 := Dup(s15, 2);
      assert s16.stack[4] == 0x32d;
      var s17 := Dup(s16, 3);
      assert s17.stack[5] == 0x32d;
      var s18 := PushN(s17, 1, 0x20);
      assert s18.stack[6] == 0x32d;
      var s19 := PushN(s18, 1, 0x01);
      assert s19.stack[7] == 0x32d;
      var s20 := Dup(s19, 3);
      assert s20.stack[8] == 0x32d;
      var s21 := Sub(s20);
      assert s21.stack[7] == 0x32d;
      var s22 := Mod(s21);
      assert s22.stack[6] == 0x32d;
      var s23 := PushN(s22, 1, 0x1f);
      assert s23.stack[7] == 0x32d;
      var s24 := Dup(s23, 3);
      assert s24.stack[8] == 0x32d;
      var s25 := Add(s24);
      assert s25.stack[7] == 0x32d;
      var s26 := Sub(s25);
      assert s26.stack[6] == 0x32d;
      var s27 := Swap(s26, 1);
      assert s27.stack[6] == 0x32d;
      var s28 := Pop(s27);
      assert s28.stack[5] == 0x32d;
      var s29 := Sub(s28);
      assert s29.stack[4] == 0x32d;
      var s30 := CallDataSize(s29);
      assert s30.stack[5] == 0x32d;
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s185(s31, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 328
    * Starting at 0x1a2e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataCopy(s0);
      assert s1.stack[3] == 0x32d;
      var s2 := Pop(s1);
      assert s2.stack[2] == 0x32d;
      var s3 := Pop(s2);
      assert s3.stack[1] == 0x32d;
      var s4 := PushN(s3, 4, 0x08c379a0);
      assert s4.stack[2] == 0x32d;
      var s5 := PushN(s4, 2, 0x0320);
      assert s5.stack[3] == 0x32d;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0x32d;
      var s7 := PushN(s6, 1, 0x20);
      assert s7.stack[2] == 0x32d;
      var s8 := PushN(s7, 2, 0x0340);
      assert s8.stack[3] == 0x32d;
      var s9 := MStore(s8);
      assert s9.stack[1] == 0x32d;
      var s10 := PushN(s9, 2, 0x0360);
      assert s10.stack[2] == 0x32d;
      var s11 := MLoad(s10);
      assert s11.stack[2] == 0x32d;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[3] == 0x32d;
      var s13 := PushN(s12, 1, 0x01);
      assert s13.stack[4] == 0x32d;
      var s14 := Dup(s13, 3);
      assert s14.stack[5] == 0x32d;
      var s15 := Sub(s14);
      assert s15.stack[4] == 0x32d;
      var s16 := Mod(s15);
      assert s16.stack[3] == 0x32d;
      var s17 := PushN(s16, 1, 0x1f);
      assert s17.stack[4] == 0x32d;
      var s18 := Dup(s17, 3);
      assert s18.stack[5] == 0x32d;
      var s19 := Add(s18);
      assert s19.stack[4] == 0x32d;
      var s20 := Sub(s19);
      assert s20.stack[3] == 0x32d;
      var s21 := Swap(s20, 1);
      assert s21.stack[3] == 0x32d;
      var s22 := Pop(s21);
      assert s22.stack[2] == 0x32d;
      var s23 := PushN(s22, 1, 0x44);
      assert s23.stack[3] == 0x32d;
      var s24 := Add(s23);
      assert s24.stack[2] == 0x32d;
      var s25 := PushN(s24, 2, 0x033c);
      assert s25.stack[3] == 0x32d;
      var s26 := Revert(s25);
      // Segment is terminal (Revert, Stop or Return)
      s26
  }

  /** Node 186
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x32d;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[8] == 0x32d;
      var s3 := Dup(s2, 1);
      assert s3.stack[9] == 0x32d;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 187
    * Segment Id for this node is: 323
    * Starting at 0x19bb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x32d;
      var s2 := PushN(s1, 1, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s132(s2, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x32d;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[6] == 0x32d;
      var s3 := Dup(s2, 1);
      assert s3.stack[7] == 0x32d;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 189
    * Segment Id for this node is: 318
    * Starting at 0x1969
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1969 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x32d;
      var s2 := PushN(s1, 2, 0x0320);
      assert s2.stack[4] == 0x32d;
      var s3 := MLoad(s2);
      assert s3.stack[4] == 0x32d;
      var s4 := PushN(s3, 2, 0x0380);
      assert s4.stack[5] == 0x32d;
      var s5 := MLoad(s4);
      assert s5.stack[5] == 0x32d;
      var s6 := Dup(s5, 1);
      assert s6.stack[6] == 0x32d;
      var s7 := Dup(s6, 3);
      assert s7.stack[7] == 0x32d;
      var s8 := Lt(s7);
      assert s8.stack[6] == 0x32d;
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      assert s9.stack[7] == 0x32d;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s10, gas - 1)
      else
        ExecuteFromCFGNode_s190(s10, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 319
    * Starting at 0x1979
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1979 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[6] == 0x32d;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0x32d;
      var s3 := Sub(s2);
      assert s3.stack[6] == 0x32d;
      var s4 := Swap(s3, 1);
      assert s4.stack[6] == 0x32d;
      var s5 := Pop(s4);
      assert s5.stack[5] == 0x32d;
      var s6 := Swap(s5, 1);
      assert s6.stack[5] == 0x32d;
      var s7 := Pop(s6);
      assert s7.stack[4] == 0x32d;
      var s8 := PushN(s7, 2, 0x0340);
      assert s8.stack[5] == 0x32d;
      var s9 := MStore(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s129(s9, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x32d;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[7] == 0x32d;
      var s3 := Dup(s2, 1);
      assert s3.stack[8] == 0x32d;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 192
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0x32d;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[9] == 0x32d;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x32d;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 193
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x184a

    requires s0.stack[8] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x184a;
      assert s1.stack[8] == 0x32d;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[7] == 0x184a;
      assert s2.stack[9] == 0x32d;
      var s3 := Dup(s2, 1);
      assert s3.stack[8] == 0x184a;
      assert s3.stack[10] == 0x32d;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 194
    * Segment Id for this node is: 297
    * Starting at 0x1772
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1772 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x184a;
      assert s1.stack[7] == 0x32d;
      var s2 := PushN(s1, 2, 0x0220);
      assert s2.stack[6] == 0x184a;
      assert s2.stack[8] == 0x32d;
      var s3 := MLoad(s2);
      assert s3.stack[6] == 0x184a;
      assert s3.stack[8] == 0x32d;
      var s4 := PushN(s3, 2, 0x0140);
      assert s4.stack[7] == 0x184a;
      assert s4.stack[9] == 0x32d;
      var s5 := PushN(s4, 2, 0x01e0);
      assert s5.stack[8] == 0x184a;
      assert s5.stack[10] == 0x32d;
      var s6 := MLoad(s5);
      assert s6.stack[8] == 0x184a;
      assert s6.stack[10] == 0x32d;
      var s7 := PushN(s6, 1, 0x03);
      assert s7.stack[9] == 0x184a;
      assert s7.stack[11] == 0x32d;
      var s8 := Dup(s7, 2);
      assert s8.stack[10] == 0x184a;
      assert s8.stack[12] == 0x32d;
      var s9 := Lt(s8);
      assert s9.stack[9] == 0x184a;
      assert s9.stack[11] == 0x32d;
      var s10 := IsZero(s9);
      assert s10.stack[9] == 0x184a;
      assert s10.stack[11] == 0x32d;
      var s11 := PushN(s10, 2, 0x1a5b);
      assert s11.stack[0] == 0x1a5b;
      assert s11.stack[10] == 0x184a;
      assert s11.stack[12] == 0x32d;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s12, gas - 1)
      else
        ExecuteFromCFGNode_s195(s12, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 298
    * Starting at 0x1787
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1787 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x184a

    requires s0.stack[10] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[9] == 0x184a;
      assert s1.stack[11] == 0x32d;
      var s2 := Mul(s1);
      assert s2.stack[8] == 0x184a;
      assert s2.stack[10] == 0x32d;
      var s3 := Add(s2);
      assert s3.stack[7] == 0x184a;
      assert s3.stack[9] == 0x32d;
      var s4 := MStore(s3);
      assert s4.stack[5] == 0x184a;
      assert s4.stack[7] == 0x32d;
      var s5 := PushN(s4, 2, 0x01e0);
      assert s5.stack[6] == 0x184a;
      assert s5.stack[8] == 0x32d;
      var s6 := Dup(s5, 1);
      assert s6.stack[7] == 0x184a;
      assert s6.stack[9] == 0x32d;
      var s7 := MLoad(s6);
      assert s7.stack[7] == 0x184a;
      assert s7.stack[9] == 0x32d;
      var s8 := PushN(s7, 1, 0x01);
      assert s8.stack[8] == 0x184a;
      assert s8.stack[10] == 0x32d;
      var s9 := Dup(s8, 1);
      assert s9.stack[9] == 0x184a;
      assert s9.stack[11] == 0x32d;
      var s10 := Dup(s9, 3);
      assert s10.stack[10] == 0x184a;
      assert s10.stack[12] == 0x32d;
      var s11 := Lt(s10);
      assert s11.stack[9] == 0x184a;
      assert s11.stack[11] == 0x32d;
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      assert s12.stack[10] == 0x184a;
      assert s12.stack[12] == 0x32d;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s13, gas - 1)
      else
        ExecuteFromCFGNode_s196(s13, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 299
    * Starting at 0x179a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x179a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x184a

    requires s0.stack[10] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[9] == 0x184a;
      assert s1.stack[11] == 0x32d;
      var s2 := Dup(s1, 3);
      assert s2.stack[10] == 0x184a;
      assert s2.stack[12] == 0x32d;
      var s3 := Sub(s2);
      assert s3.stack[9] == 0x184a;
      assert s3.stack[11] == 0x32d;
      var s4 := Swap(s3, 1);
      assert s4.stack[9] == 0x184a;
      assert s4.stack[11] == 0x32d;
      var s5 := Pop(s4);
      assert s5.stack[8] == 0x184a;
      assert s5.stack[10] == 0x32d;
      var s6 := Swap(s5, 1);
      assert s6.stack[8] == 0x184a;
      assert s6.stack[10] == 0x32d;
      var s7 := Pop(s6);
      assert s7.stack[7] == 0x184a;
      assert s7.stack[9] == 0x32d;
      var s8 := Dup(s7, 2);
      assert s8.stack[8] == 0x184a;
      assert s8.stack[10] == 0x32d;
      var s9 := MStore(s8);
      assert s9.stack[6] == 0x184a;
      assert s9.stack[8] == 0x32d;
      var s10 := Pop(s9);
      assert s10.stack[5] == 0x184a;
      assert s10.stack[7] == 0x32d;
      var s11 := PushN(s10, 2, 0x01e0);
      assert s11.stack[6] == 0x184a;
      assert s11.stack[8] == 0x32d;
      var s12 := MLoad(s11);
      assert s12.stack[6] == 0x184a;
      assert s12.stack[8] == 0x32d;
      var s13 := PushN(s12, 2, 0x17b0);
      assert s13.stack[0] == 0x17b0;
      assert s13.stack[7] == 0x184a;
      assert s13.stack[9] == 0x32d;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s14, gas - 1)
      else
        ExecuteFromCFGNode_s197(s14, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 300
    * Starting at 0x17ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x17c0);
      assert s1.stack[0] == 0x17c0;
      assert s1.stack[6] == 0x184a;
      assert s1.stack[8] == 0x32d;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s2, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 301
    * Starting at 0x17b0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x184a;
      assert s1.stack[7] == 0x32d;
      var s2 := Dup(s1, 2);
      assert s2.stack[6] == 0x184a;
      assert s2.stack[8] == 0x32d;
      var s3 := MLoad(s2);
      assert s3.stack[6] == 0x184a;
      assert s3.stack[8] == 0x32d;
      var s4 := PushN(s3, 1, 0x01);
      assert s4.stack[7] == 0x184a;
      assert s4.stack[9] == 0x32d;
      var s5 := Add(s4);
      assert s5.stack[6] == 0x184a;
      assert s5.stack[8] == 0x32d;
      var s6 := Dup(s5, 1);
      assert s6.stack[7] == 0x184a;
      assert s6.stack[9] == 0x32d;
      var s7 := Dup(s6, 4);
      assert s7.stack[8] == 0x184a;
      assert s7.stack[10] == 0x32d;
      var s8 := MStore(s7);
      assert s8.stack[6] == 0x184a;
      assert s8.stack[8] == 0x32d;
      var s9 := Dup(s8, 2);
      assert s9.stack[7] == 0x184a;
      assert s9.stack[9] == 0x32d;
      var s10 := Eq(s9);
      assert s10.stack[6] == 0x184a;
      assert s10.stack[8] == 0x32d;
      var s11 := IsZero(s10);
      assert s11.stack[6] == 0x184a;
      assert s11.stack[8] == 0x32d;
      var s12 := PushN(s11, 2, 0x1736);
      assert s12.stack[0] == 0x1736;
      assert s12.stack[7] == 0x184a;
      assert s12.stack[9] == 0x32d;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s13, gas - 1)
      else
        ExecuteFromCFGNode_s115(s13, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x184a

    requires s0.stack[10] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0x184a;
      assert s1.stack[10] == 0x32d;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[9] == 0x184a;
      assert s2.stack[11] == 0x32d;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x184a;
      assert s3.stack[12] == 0x32d;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 200
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x184a

    requires s0.stack[9] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x184a;
      assert s1.stack[9] == 0x32d;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[8] == 0x184a;
      assert s2.stack[10] == 0x32d;
      var s3 := Dup(s2, 1);
      assert s3.stack[9] == 0x184a;
      assert s3.stack[11] == 0x32d;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 201
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x184a

    requires s0.stack[7] == 0x32d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x184a;
      assert s1.stack[7] == 0x32d;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[6] == 0x184a;
      assert s2.stack[8] == 0x32d;
      var s3 := Dup(s2, 1);
      assert s3.stack[7] == 0x184a;
      assert s3.stack[9] == 0x32d;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 202
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
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

  /** Node 203
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
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

  /** Node 204
    * Segment Id for this node is: 38
    * Starting at 0x274
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x274 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 14, 0x314dc6448d9338c15b0a00000001);
      var s3 := PushN(s2, 2, 0x0400);
      var s4 := MLoad(s3);
      var s5 := Lt(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s98(s5, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x243;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[7] == 0x243;
      var s3 := Dup(s2, 1);
      assert s3.stack[8] == 0x243;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 206
    * Segment Id for this node is: 297
    * Starting at 0x1772
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1772 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x243;
      var s2 := PushN(s1, 2, 0x0220);
      assert s2.stack[6] == 0x243;
      var s3 := MLoad(s2);
      assert s3.stack[6] == 0x243;
      var s4 := PushN(s3, 2, 0x0140);
      assert s4.stack[7] == 0x243;
      var s5 := PushN(s4, 2, 0x01e0);
      assert s5.stack[8] == 0x243;
      var s6 := MLoad(s5);
      assert s6.stack[8] == 0x243;
      var s7 := PushN(s6, 1, 0x03);
      assert s7.stack[9] == 0x243;
      var s8 := Dup(s7, 2);
      assert s8.stack[10] == 0x243;
      var s9 := Lt(s8);
      assert s9.stack[9] == 0x243;
      var s10 := IsZero(s9);
      assert s10.stack[9] == 0x243;
      var s11 := PushN(s10, 2, 0x1a5b);
      assert s11.stack[0] == 0x1a5b;
      assert s11.stack[10] == 0x243;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s211(s12, gas - 1)
      else
        ExecuteFromCFGNode_s207(s12, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 298
    * Starting at 0x1787
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1787 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[9] == 0x243;
      var s2 := Mul(s1);
      assert s2.stack[8] == 0x243;
      var s3 := Add(s2);
      assert s3.stack[7] == 0x243;
      var s4 := MStore(s3);
      assert s4.stack[5] == 0x243;
      var s5 := PushN(s4, 2, 0x01e0);
      assert s5.stack[6] == 0x243;
      var s6 := Dup(s5, 1);
      assert s6.stack[7] == 0x243;
      var s7 := MLoad(s6);
      assert s7.stack[7] == 0x243;
      var s8 := PushN(s7, 1, 0x01);
      assert s8.stack[8] == 0x243;
      var s9 := Dup(s8, 1);
      assert s9.stack[9] == 0x243;
      var s10 := Dup(s9, 3);
      assert s10.stack[10] == 0x243;
      var s11 := Lt(s10);
      assert s11.stack[9] == 0x243;
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      assert s12.stack[10] == 0x243;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s211(s13, gas - 1)
      else
        ExecuteFromCFGNode_s208(s13, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 299
    * Starting at 0x179a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x179a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[9] == 0x243;
      var s2 := Dup(s1, 3);
      assert s2.stack[10] == 0x243;
      var s3 := Sub(s2);
      assert s3.stack[9] == 0x243;
      var s4 := Swap(s3, 1);
      assert s4.stack[9] == 0x243;
      var s5 := Pop(s4);
      assert s5.stack[8] == 0x243;
      var s6 := Swap(s5, 1);
      assert s6.stack[8] == 0x243;
      var s7 := Pop(s6);
      assert s7.stack[7] == 0x243;
      var s8 := Dup(s7, 2);
      assert s8.stack[8] == 0x243;
      var s9 := MStore(s8);
      assert s9.stack[6] == 0x243;
      var s10 := Pop(s9);
      assert s10.stack[5] == 0x243;
      var s11 := PushN(s10, 2, 0x01e0);
      assert s11.stack[6] == 0x243;
      var s12 := MLoad(s11);
      assert s12.stack[6] == 0x243;
      var s13 := PushN(s12, 2, 0x17b0);
      assert s13.stack[0] == 0x17b0;
      assert s13.stack[7] == 0x243;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s210(s14, gas - 1)
      else
        ExecuteFromCFGNode_s209(s14, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 300
    * Starting at 0x17ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x17c0);
      assert s1.stack[0] == 0x17c0;
      assert s1.stack[6] == 0x243;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s2, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 301
    * Starting at 0x17b0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x243;
      var s2 := Dup(s1, 2);
      assert s2.stack[6] == 0x243;
      var s3 := MLoad(s2);
      assert s3.stack[6] == 0x243;
      var s4 := PushN(s3, 1, 0x01);
      assert s4.stack[7] == 0x243;
      var s5 := Add(s4);
      assert s5.stack[6] == 0x243;
      var s6 := Dup(s5, 1);
      assert s6.stack[7] == 0x243;
      var s7 := Dup(s6, 4);
      assert s7.stack[8] == 0x243;
      var s8 := MStore(s7);
      assert s8.stack[6] == 0x243;
      var s9 := Dup(s8, 2);
      assert s9.stack[7] == 0x243;
      var s10 := Eq(s9);
      assert s10.stack[6] == 0x243;
      var s11 := IsZero(s10);
      assert s11.stack[6] == 0x243;
      var s12 := PushN(s11, 2, 0x1736);
      assert s12.stack[0] == 0x1736;
      assert s12.stack[7] == 0x243;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s13, gas - 1)
      else
        ExecuteFromCFGNode_s93(s13, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0x243;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[9] == 0x243;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x243;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 212
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x243;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[8] == 0x243;
      var s3 := Dup(s2, 1);
      assert s3.stack[9] == 0x243;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 213
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x243

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x243;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[6] == 0x243;
      var s3 := Dup(s2, 1);
      assert s3.stack[7] == 0x243;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 214
    * Segment Id for this node is: 33
    * Starting at 0x212
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x212 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 7, 0xb1a2bc2ec50001);
      var s3 := PushN(s2, 1, 0x24);
      var s4 := CallDataLoad(s3);
      var s5 := Lt(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s84(s5, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 29
    * Starting at 0x1ee
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x1017df81);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := CallDataLoad(s3);
      var s5 := Lt(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s81(s5, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 129
    * Starting at 0xa09
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa09 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x36bc8855);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x128e);
      assert s5.stack[0] == 0x128e;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s336(s6, gas - 1)
      else
        ExecuteFromCFGNode_s217(s6, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 130
    * Starting at 0xa15
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa15 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0a8b);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := Gt(s3);
      var s5 := PushN(s4, 2, 0x0a26);
      assert s5.stack[0] == 0xa26;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s335(s6, gas - 1)
      else
        ExecuteFromCFGNode_s218(s6, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 131
    * Starting at 0xa20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 2, 0x0a30);
      assert s2.stack[0] == 0xa30;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s3, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 133
    * Starting at 0xa30
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := IsZero(s1);
      var s3 := PushN(s2, 2, 0x1a5b);
      assert s3.stack[0] == 0x1a5b;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s4, gas - 1)
      else
        ExecuteFromCFGNode_s220(s4, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 134
    * Starting at 0xa36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 5, 0x02540be3ff);
      var s2 := PushN(s1, 1, 0x24);
      var s3 := CallDataLoad(s2);
      var s4 := Gt(s3);
      var s5 := PushN(s4, 2, 0x0a4a);
      assert s5.stack[0] == 0xa4a;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s334(s6, gas - 1)
      else
        ExecuteFromCFGNode_s221(s6, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 135
    * Starting at 0xa44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 2, 0x0a57);
      assert s2.stack[0] == 0xa57;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s3, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 137
    * Starting at 0xa57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := IsZero(s1);
      var s3 := PushN(s2, 2, 0x1a5b);
      assert s3.stack[0] == 0x1a5b;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s4, gas - 1)
      else
        ExecuteFromCFGNode_s223(s4, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 138
    * Starting at 0xa5d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 8, 0x016345785d89ffff);
      var s2 := PushN(s1, 1, 0xa4);
      var s3 := CallDataLoad(s2);
      var s4 := Gt(s3);
      var s5 := PushN(s4, 2, 0x0a74);
      assert s5.stack[0] == 0xa74;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s333(s6, gas - 1)
      else
        ExecuteFromCFGNode_s224(s6, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 139
    * Starting at 0xa6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 2, 0x0a88);
      assert s2.stack[0] == 0xa88;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s3, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 141
    * Starting at 0xa88
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := IsZero(s1);
      var s3 := PushN(s2, 2, 0x1a5b);
      assert s3.stack[0] == 0x1a5b;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s4, gas - 1)
      else
        ExecuteFromCFGNode_s226(s4, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 142
    * Starting at 0xa8e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0240);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x03);
      var s4 := Dup(s3, 2);
      var s5 := Dup(s4, 4);
      var s6 := MStore(s5);
      var s7 := Add(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s227(s7, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 143
    * Starting at 0xa99
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0xc4);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 2, 0x0240);
      var s5 := MLoad(s4);
      var s6 := Eq(s5);
      var s7 := PushN(s6, 2, 0x0b0f);
      assert s7.stack[0] == 0xb0f;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s233(s8, gas - 1)
      else
        ExecuteFromCFGNode_s228(s8, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 144
    * Starting at 0xaa6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := PushN(s1, 2, 0x0240);
      var s3 := MLoad(s2);
      var s4 := Mul(s3);
      var s5 := PushN(s4, 1, 0x44);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := PushN(s7, 8, 0x0de0b6b3a7640000);
      var s9 := Dup(s8, 1);
      var s10 := Dup(s9, 3);
      var s11 := Mul(s10);
      var s12 := Dup(s11, 3);
      var s13 := IsZero(s12);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := Dup(s15, 4);
      var s17 := Div(s16);
      var s18 := Eq(s17);
      var s19 := Or(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x1a5b);
      assert s21.stack[0] == 0x1a5b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s22, gas - 1)
      else
        ExecuteFromCFGNode_s229(s22, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 145
    * Starting at 0xaca
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0xa4);
      var s6 := CallDataLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s230(s11, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 146
    * Starting at 0xad8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0260);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 7, 0x2386f26fc0ffff);
      var s10 := PushN(s9, 2, 0x0260);
      var s11 := MLoad(s10);
      var s12 := Gt(s11);
      var s13 := PushN(s12, 2, 0x0af9);
      assert s13.stack[0] == 0xaf9;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s332(s14, gas - 1)
      else
        ExecuteFromCFGNode_s231(s14, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 147
    * Starting at 0xaf3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 2, 0x0b09);
      assert s2.stack[0] == 0xb09;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s3, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 149
    * Starting at 0xb09
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb09 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := IsZero(s1);
      var s3 := PushN(s2, 2, 0x1a5b);
      assert s3.stack[0] == 0x1a5b;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s4, gas - 1)
      else
        ExecuteFromCFGNode_s233(s4, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 150
    * Starting at 0xb0f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0f as nat
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
      var s12 := PushN(s11, 2, 0x0a99);
      assert s12.stack[0] == 0xa99;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s227(s13, gas - 1)
      else
        ExecuteFromCFGNode_s234(s13, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 151
    * Starting at 0xb1f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0xa4);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 1, 0x03);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Div(s7);
      var s9 := Swap(s8, 1);
      var s10 := Pop(s9);
      var s11 := Swap(s10, 1);
      var s12 := Pop(s11);
      var s13 := PushN(s12, 2, 0x0240);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 8, 0x0de0b6b3a7640000);
      var s16 := PushN(s15, 2, 0x0260);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 1, 0x00);
      var s19 := PushN(s18, 2, 0x0280);
      var s20 := MStore(s19);
      var s21 := PushN(s20, 1, 0x44);
      var s22 := CallDataLoad(s21);
      var s23 := PushN(s22, 2, 0x02a0);
      var s24 := MStore(s23);
      var s25 := PushN(s24, 1, 0x64);
      var s26 := CallDataLoad(s25);
      var s27 := PushN(s26, 2, 0x02c0);
      var s28 := MStore(s27);
      var s29 := PushN(s28, 1, 0x84);
      assert s29.stack[0] == 0x84;
      var s30 := CallDataLoad(s29);
      var s31 := PushN(s30, 2, 0x02e0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s235(s31, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 152
    * Starting at 0xb58
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 2, 0x02a0);
      var s4 := PushN(s3, 1, 0xc4);
      var s5 := CallDataLoad(s4);
      var s6 := PushN(s5, 1, 0x03);
      var s7 := Dup(s6, 2);
      var s8 := Lt(s7);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s11, gas - 1)
      else
        ExecuteFromCFGNode_s236(s11, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 153
    * Starting at 0xb6a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6a as nat
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
      var s5 := PushN(s4, 2, 0x02a0);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 1, 0xe0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x02c0);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x0100);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 2, 0x02e0);
      var s14 := MLoad(s13);
      var s15 := PushN(s14, 2, 0x0120);
      var s16 := MStore(s15);
      var s17 := PushN(s16, 2, 0x0b90);
      assert s17.stack[0] == 0xb90;
      var s18 := PushN(s17, 2, 0x0300);
      assert s18.stack[1] == 0xb90;
      var s19 := PushN(s18, 2, 0x16e6);
      assert s19.stack[0] == 0x16e6;
      assert s19.stack[2] == 0xb90;
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s20, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 290
    * Starting at 0x16e6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0xb90;
      var s2 := PushN(s1, 1, 0xe0);
      assert s2.stack[2] == 0xb90;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0xb90;
      var s4 := PushN(s3, 2, 0x0140);
      assert s4.stack[3] == 0xb90;
      var s5 := MStore(s4);
      assert s5.stack[1] == 0xb90;
      var s6 := PushN(s5, 2, 0x0100);
      assert s6.stack[2] == 0xb90;
      var s7 := MLoad(s6);
      assert s7.stack[2] == 0xb90;
      var s8 := PushN(s7, 2, 0x0160);
      assert s8.stack[3] == 0xb90;
      var s9 := MStore(s8);
      assert s9.stack[1] == 0xb90;
      var s10 := PushN(s9, 2, 0x0120);
      assert s10.stack[2] == 0xb90;
      var s11 := MLoad(s10);
      assert s11.stack[2] == 0xb90;
      var s12 := PushN(s11, 2, 0x0180);
      assert s12.stack[3] == 0xb90;
      var s13 := MStore(s12);
      assert s13.stack[1] == 0xb90;
      var s14 := PushN(s13, 2, 0x01a0);
      assert s14.stack[2] == 0xb90;
      var s15 := PushN(s14, 1, 0x01);
      assert s15.stack[3] == 0xb90;
      var s16 := PushN(s15, 1, 0x02);
      assert s16.stack[4] == 0xb90;
      var s17 := Dup(s16, 2);
      assert s17.stack[5] == 0xb90;
      var s18 := Dup(s17, 4);
      assert s18.stack[6] == 0xb90;
      var s19 := MStore(s18);
      assert s19.stack[4] == 0xb90;
      var s20 := Add(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s238(s20, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 291
    * Starting at 0x1709
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1709 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0xb90;
      var s2 := PushN(s1, 2, 0x0140);
      assert s2.stack[4] == 0xb90;
      var s3 := PushN(s2, 2, 0x01a0);
      assert s3.stack[5] == 0xb90;
      var s4 := MLoad(s3);
      assert s4.stack[5] == 0xb90;
      var s5 := PushN(s4, 1, 0x03);
      assert s5.stack[6] == 0xb90;
      var s6 := Dup(s5, 2);
      assert s6.stack[7] == 0xb90;
      var s7 := Lt(s6);
      assert s7.stack[6] == 0xb90;
      var s8 := IsZero(s7);
      assert s8.stack[6] == 0xb90;
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      assert s9.stack[7] == 0xb90;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s331(s10, gas - 1)
      else
        ExecuteFromCFGNode_s239(s10, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 292
    * Starting at 0x171a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x171a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[6] == 0xb90;
      var s2 := Mul(s1);
      assert s2.stack[5] == 0xb90;
      var s3 := Add(s2);
      assert s3.stack[4] == 0xb90;
      var s4 := MLoad(s3);
      assert s4.stack[4] == 0xb90;
      var s5 := PushN(s4, 2, 0x01c0);
      assert s5.stack[5] == 0xb90;
      var s6 := MStore(s5);
      assert s6.stack[3] == 0xb90;
      var s7 := PushN(s6, 2, 0x01a0);
      assert s7.stack[4] == 0xb90;
      var s8 := MLoad(s7);
      assert s8.stack[4] == 0xb90;
      var s9 := PushN(s8, 2, 0x01e0);
      assert s9.stack[5] == 0xb90;
      var s10 := MStore(s9);
      assert s10.stack[3] == 0xb90;
      var s11 := PushN(s10, 2, 0x0200);
      assert s11.stack[4] == 0xb90;
      var s12 := PushN(s11, 1, 0x00);
      assert s12.stack[5] == 0xb90;
      var s13 := PushN(s12, 1, 0x03);
      assert s13.stack[6] == 0xb90;
      var s14 := Dup(s13, 2);
      assert s14.stack[7] == 0xb90;
      var s15 := Dup(s14, 4);
      assert s15.stack[8] == 0xb90;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0xb90;
      var s17 := Add(s16);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s240(s17, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 293
    * Starting at 0x1736
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1736 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0xb90;
      var s2 := PushN(s1, 2, 0x0140);
      assert s2.stack[6] == 0xb90;
      var s3 := PushN(s2, 2, 0x01e0);
      assert s3.stack[7] == 0xb90;
      var s4 := MLoad(s3);
      assert s4.stack[7] == 0xb90;
      var s5 := PushN(s4, 1, 0x01);
      assert s5.stack[8] == 0xb90;
      var s6 := Dup(s5, 1);
      assert s6.stack[9] == 0xb90;
      var s7 := Dup(s6, 3);
      assert s7.stack[10] == 0xb90;
      var s8 := Lt(s7);
      assert s8.stack[9] == 0xb90;
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      assert s9.stack[10] == 0xb90;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s329(s10, gas - 1)
      else
        ExecuteFromCFGNode_s241(s10, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 294
    * Starting at 0x1747
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1747 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[9] == 0xb90;
      var s2 := Dup(s1, 3);
      assert s2.stack[10] == 0xb90;
      var s3 := Sub(s2);
      assert s3.stack[9] == 0xb90;
      var s4 := Swap(s3, 1);
      assert s4.stack[9] == 0xb90;
      var s5 := Pop(s4);
      assert s5.stack[8] == 0xb90;
      var s6 := Swap(s5, 1);
      assert s6.stack[8] == 0xb90;
      var s7 := Pop(s6);
      assert s7.stack[7] == 0xb90;
      var s8 := PushN(s7, 1, 0x03);
      assert s8.stack[8] == 0xb90;
      var s9 := Dup(s8, 2);
      assert s9.stack[9] == 0xb90;
      var s10 := Lt(s9);
      assert s10.stack[8] == 0xb90;
      var s11 := IsZero(s10);
      assert s11.stack[8] == 0xb90;
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      assert s12.stack[9] == 0xb90;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s330(s13, gas - 1)
      else
        ExecuteFromCFGNode_s242(s13, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 295
    * Starting at 0x1757
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1757 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[8] == 0xb90;
      var s2 := Mul(s1);
      assert s2.stack[7] == 0xb90;
      var s3 := Add(s2);
      assert s3.stack[6] == 0xb90;
      var s4 := MLoad(s3);
      assert s4.stack[6] == 0xb90;
      var s5 := PushN(s4, 2, 0x0220);
      assert s5.stack[7] == 0xb90;
      var s6 := MStore(s5);
      assert s6.stack[5] == 0xb90;
      var s7 := PushN(s6, 2, 0x01c0);
      assert s7.stack[6] == 0xb90;
      var s8 := MLoad(s7);
      assert s8.stack[6] == 0xb90;
      var s9 := PushN(s8, 2, 0x0220);
      assert s9.stack[7] == 0xb90;
      var s10 := MLoad(s9);
      assert s10.stack[7] == 0xb90;
      var s11 := Gt(s10);
      assert s11.stack[6] == 0xb90;
      var s12 := IsZero(s11);
      assert s12.stack[6] == 0xb90;
      var s13 := PushN(s12, 2, 0x1772);
      assert s13.stack[0] == 0x1772;
      assert s13.stack[7] == 0xb90;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s324(s14, gas - 1)
      else
        ExecuteFromCFGNode_s243(s14, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 296
    * Starting at 0x176e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x176e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x17c0);
      assert s1.stack[0] == 0x17c0;
      assert s1.stack[6] == 0xb90;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s2, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 302
    * Starting at 0x17c0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0xb90;
      var s2 := Pop(s1);
      assert s2.stack[4] == 0xb90;
      var s3 := Pop(s2);
      assert s3.stack[3] == 0xb90;
      var s4 := PushN(s3, 2, 0x01c0);
      assert s4.stack[4] == 0xb90;
      var s5 := MLoad(s4);
      assert s5.stack[4] == 0xb90;
      var s6 := PushN(s5, 2, 0x0140);
      assert s6.stack[5] == 0xb90;
      var s7 := PushN(s6, 2, 0x01e0);
      assert s7.stack[6] == 0xb90;
      var s8 := MLoad(s7);
      assert s8.stack[6] == 0xb90;
      var s9 := PushN(s8, 1, 0x03);
      assert s9.stack[7] == 0xb90;
      var s10 := Dup(s9, 2);
      assert s10.stack[8] == 0xb90;
      var s11 := Lt(s10);
      assert s11.stack[7] == 0xb90;
      var s12 := IsZero(s11);
      assert s12.stack[7] == 0xb90;
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      assert s13.stack[8] == 0xb90;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s323(s14, gas - 1)
      else
        ExecuteFromCFGNode_s245(s14, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 303
    * Starting at 0x17d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[7] == 0xb90;
      var s2 := Mul(s1);
      assert s2.stack[6] == 0xb90;
      var s3 := Add(s2);
      assert s3.stack[5] == 0xb90;
      var s4 := MStore(s3);
      assert s4.stack[3] == 0xb90;
      var s5 := Dup(s4, 2);
      assert s5.stack[4] == 0xb90;
      var s6 := MLoad(s5);
      assert s6.stack[4] == 0xb90;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[5] == 0xb90;
      var s8 := Add(s7);
      assert s8.stack[4] == 0xb90;
      var s9 := Dup(s8, 1);
      assert s9.stack[5] == 0xb90;
      var s10 := Dup(s9, 4);
      assert s10.stack[6] == 0xb90;
      var s11 := MStore(s10);
      assert s11.stack[4] == 0xb90;
      var s12 := Dup(s11, 2);
      assert s12.stack[5] == 0xb90;
      var s13 := Eq(s12);
      assert s13.stack[4] == 0xb90;
      var s14 := IsZero(s13);
      assert s14.stack[4] == 0xb90;
      var s15 := PushN(s14, 2, 0x1709);
      assert s15.stack[0] == 0x1709;
      assert s15.stack[5] == 0xb90;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s238(s16, gas - 1)
      else
        ExecuteFromCFGNode_s246(s16, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 304
    * Starting at 0x17eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0xb90;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0xb90;
      var s3 := PushN(s2, 2, 0x0140);
      assert s3.stack[2] == 0xb90;
      var s4 := MLoad(s3);
      assert s4.stack[2] == 0xb90;
      var s5 := Dup(s4, 2);
      assert s5.stack[3] == 0xb90;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0xb90;
      var s7 := PushN(s6, 2, 0x0160);
      assert s7.stack[2] == 0xb90;
      var s8 := MLoad(s7);
      assert s8.stack[2] == 0xb90;
      var s9 := Dup(s8, 2);
      assert s9.stack[3] == 0xb90;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[4] == 0xb90;
      var s11 := Add(s10);
      assert s11.stack[3] == 0xb90;
      var s12 := MStore(s11);
      assert s12.stack[1] == 0xb90;
      var s13 := PushN(s12, 2, 0x0180);
      assert s13.stack[2] == 0xb90;
      var s14 := MLoad(s13);
      assert s14.stack[2] == 0xb90;
      var s15 := Dup(s14, 2);
      assert s15.stack[3] == 0xb90;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[4] == 0xb90;
      var s17 := Add(s16);
      assert s17.stack[3] == 0xb90;
      var s18 := MStore(s17);
      assert s18.stack[1] == 0xb90;
      var s19 := Pop(s18);
      assert s19.stack[0] == 0xb90;
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s247(s20, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 154
    * Starting at 0xb90
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0300);
      var s3 := Dup(s2, 1);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x02a0);
      var s6 := MStore(s5);
      var s7 := Dup(s6, 1);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := Add(s8);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x02c0);
      var s12 := MStore(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 1, 0x40);
      var s15 := Add(s14);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 2, 0x02e0);
      var s18 := MStore(s17);
      var s19 := Pop(s18);
      var s20 := PushN(s19, 2, 0x02a0);
      var s21 := MLoad(s20);
      var s22 := PushN(s21, 6, 0x5af3107a4000);
      var s23 := Dup(s22, 1);
      var s24 := Dup(s23, 3);
      var s25 := Div(s24);
      var s26 := Swap(s25, 1);
      var s27 := Pop(s26);
      var s28 := Swap(s27, 1);
      var s29 := Pop(s28);
      var s30 := PushN(s29, 1, 0xa4);
      var s31 := CallDataLoad(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s248(s31, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 155
    * Starting at 0xbc2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 6, 0x5af3107a4000);
      var s2 := Dup(s1, 1);
      var s3 := Dup(s2, 3);
      var s4 := Div(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := Swap(s6, 1);
      var s8 := Pop(s7);
      var s9 := Dup(s8, 1);
      var s10 := Dup(s9, 3);
      var s11 := Lt(s10);
      var s12 := PushN(s11, 2, 0x0bdc);
      assert s12.stack[0] == 0xbdc;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s322(s13, gas - 1)
      else
        ExecuteFromCFGNode_s249(s13, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 156
    * Starting at 0xbd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x0bde);
      assert s2.stack[0] == 0xbde;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s3, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 158
    * Starting at 0xbde
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbde as nat
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
      var s6 := PushN(s5, 1, 0x64);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 3);
      var s9 := Lt(s8);
      var s10 := PushN(s9, 2, 0x0bf1);
      assert s10.stack[0] == 0xbf1;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s321(s11, gas - 1)
      else
        ExecuteFromCFGNode_s251(s11, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 159
    * Starting at 0xbec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x0bf3);
      assert s2.stack[0] == 0xbf3;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s3, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 161
    * Starting at 0xbf3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf3 as nat
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
      var s6 := PushN(s5, 2, 0x0300);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x0320);
      var s9 := PushN(s8, 1, 0x02);
      var s10 := PushN(s9, 1, 0x02);
      var s11 := Dup(s10, 2);
      var s12 := Dup(s11, 4);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s253(s14, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 162
    * Starting at 0xc07
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc07 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x02a0);
      var s3 := PushN(s2, 1, 0x03);
      var s4 := PushN(s3, 2, 0x0320);
      var s5 := MLoad(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Lt(s7);
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s10, gas - 1)
      else
        ExecuteFromCFGNode_s254(s10, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 163
    * Starting at 0xc18
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc18 as nat
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
      var s8 := PushN(s7, 1, 0x03);
      var s9 := Dup(s8, 2);
      var s10 := Lt(s9);
      var s11 := IsZero(s10);
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s13, gas - 1)
      else
        ExecuteFromCFGNode_s255(s13, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 164
    * Starting at 0xc28
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := Mul(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0340);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0240);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 1, 0xa4);
      var s10 := CallDataLoad(s9);
      var s11 := Dup(s10, 1);
      var s12 := Dup(s11, 3);
      var s13 := Mul(s12);
      var s14 := Dup(s13, 3);
      var s15 := IsZero(s14);
      var s16 := Dup(s15, 3);
      var s17 := Dup(s16, 5);
      var s18 := Dup(s17, 4);
      var s19 := Div(s18);
      var s20 := Eq(s19);
      var s21 := Or(s20);
      var s22 := IsZero(s21);
      var s23 := PushN(s22, 2, 0x1a5b);
      assert s23.stack[0] == 0x1a5b;
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s24, gas - 1)
      else
        ExecuteFromCFGNode_s256(s24, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 165
    * Starting at 0xc48
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0340);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 1, 0x03);
      var s8 := Dup(s7, 1);
      var s9 := Dup(s8, 3);
      var s10 := Mul(s9);
      var s11 := Dup(s10, 3);
      var s12 := IsZero(s11);
      var s13 := Dup(s12, 3);
      var s14 := Dup(s13, 5);
      var s15 := Dup(s14, 4);
      var s16 := Div(s15);
      var s17 := Eq(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := PushN(s19, 2, 0x1a5b);
      assert s20.stack[0] == 0x1a5b;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s21, gas - 1)
      else
        ExecuteFromCFGNode_s257(s21, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 166
    * Starting at 0xc62
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 1);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x1a5b);
      assert s8.stack[0] == 0x1a5b;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s9, gas - 1)
      else
        ExecuteFromCFGNode_s258(s9, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 167
    * Starting at 0xc6d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0240);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0280);
      var s10 := Dup(s9, 1);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 2, 0x0340);
      var s13 := MLoad(s12);
      var s14 := Dup(s13, 2);
      var s15 := Dup(s14, 2);
      var s16 := Dup(s15, 4);
      var s17 := Add(s16);
      var s18 := Lt(s17);
      var s19 := PushN(s18, 2, 0x1a5b);
      assert s19.stack[0] == 0x1a5b;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s20, gas - 1)
      else
        ExecuteFromCFGNode_s259(s20, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 168
    * Starting at 0xc89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := Dup(s7, 2);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      var s11 := Dup(s10, 2);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 1, 0x01);
      var s14 := Add(s13);
      var s15 := Dup(s14, 1);
      var s16 := Dup(s15, 4);
      var s17 := MStore(s16);
      var s18 := Dup(s17, 2);
      var s19 := Eq(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x0c07);
      assert s21.stack[0] == 0xc07;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s253(s22, gas - 1)
      else
        ExecuteFromCFGNode_s260(s22, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 169
    * Starting at 0xca2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0320);
      var s4 := PushN(s3, 1, 0x00);
      var s5 := PushN(s4, 1, 0x02);
      var s6 := Dup(s5, 2);
      var s7 := Dup(s6, 4);
      var s8 := MStore(s7);
      var s9 := Add(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s261(s9, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 170
    * Starting at 0xcaf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0260);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x02a0);
      var s5 := PushN(s4, 2, 0x0320);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 1, 0x03);
      var s8 := Dup(s7, 2);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := PushN(s10, 2, 0x1a5b);
      assert s11.stack[0] == 0x1a5b;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s12, gas - 1)
      else
        ExecuteFromCFGNode_s262(s12, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 171
    * Starting at 0xcc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := Mul(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Mul(s6);
      var s8 := Dup(s7, 3);
      var s9 := IsZero(s8);
      var s10 := Dup(s9, 3);
      var s11 := Dup(s10, 5);
      var s12 := Dup(s11, 4);
      var s13 := Div(s12);
      var s14 := Eq(s13);
      var s15 := Or(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x1a5b);
      assert s17.stack[0] == 0x1a5b;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s18, gas - 1)
      else
        ExecuteFromCFGNode_s263(s18, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 172
    * Starting at 0xcd9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x03);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Mul(s7);
      var s9 := Dup(s8, 3);
      var s10 := IsZero(s9);
      var s11 := Dup(s10, 3);
      var s12 := Dup(s11, 5);
      var s13 := Dup(s12, 4);
      var s14 := Div(s13);
      var s15 := Eq(s14);
      var s16 := Or(s15);
      var s17 := IsZero(s16);
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s19, gas - 1)
      else
        ExecuteFromCFGNode_s264(s19, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 173
    * Starting at 0xcef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0xa4);
      var s6 := CallDataLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s265(s11, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 174
    * Starting at 0xcfd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0260);
      var s8 := MStore(s7);
      var s9 := Dup(s8, 2);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 1, 0x01);
      var s12 := Add(s11);
      var s13 := Dup(s12, 1);
      var s14 := Dup(s13, 4);
      var s15 := MStore(s14);
      var s16 := Dup(s15, 2);
      var s17 := Eq(s16);
      var s18 := IsZero(s17);
      var s19 := PushN(s18, 2, 0x0caf);
      assert s19.stack[0] == 0xcaf;
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s261(s20, gas - 1)
      else
        ExecuteFromCFGNode_s266(s20, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 175
    * Starting at 0xd16
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0320);
      var s4 := PushN(s3, 1, 0x00);
      var s5 := PushN(s4, 1, 0xff);
      var s6 := Dup(s5, 2);
      var s7 := Dup(s6, 4);
      var s8 := MStore(s7);
      var s9 := Add(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s267(s9, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 176
    * Starting at 0xd23
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0240);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0340);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 2, 0x0260);
      var s7 := MLoad(s6);
      var s8 := PushN(s7, 2, 0x0240);
      var s9 := MLoad(s8);
      var s10 := Dup(s9, 1);
      var s11 := Dup(s10, 3);
      var s12 := Mul(s11);
      var s13 := Dup(s12, 3);
      var s14 := IsZero(s13);
      var s15 := Dup(s14, 3);
      var s16 := Dup(s15, 5);
      var s17 := Dup(s16, 4);
      var s18 := Div(s17);
      var s19 := Eq(s18);
      var s20 := Or(s19);
      var s21 := IsZero(s20);
      var s22 := PushN(s21, 2, 0x1a5b);
      assert s22.stack[0] == 0x1a5b;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s23, gas - 1)
      else
        ExecuteFromCFGNode_s268(s23, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 177
    * Starting at 0xd44
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x03);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Mul(s7);
      var s9 := Dup(s8, 3);
      var s10 := IsZero(s9);
      var s11 := Dup(s10, 3);
      var s12 := Dup(s11, 5);
      var s13 := Dup(s12, 4);
      var s14 := Div(s13);
      var s15 := Eq(s14);
      var s16 := Or(s15);
      var s17 := IsZero(s16);
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s19, gas - 1)
      else
        ExecuteFromCFGNode_s269(s19, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 178
    * Starting at 0xd5a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0xa4);
      var s6 := CallDataLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s270(s11, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 179
    * Starting at 0xd68
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0360);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0280);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x0240);
      var s12 := MLoad(s11);
      var s13 := Dup(s12, 2);
      var s14 := Dup(s13, 2);
      var s15 := Dup(s14, 4);
      var s16 := Add(s15);
      var s17 := Lt(s16);
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s19, gas - 1)
      else
        ExecuteFromCFGNode_s271(s19, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 180
    * Starting at 0xd83
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0380);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 8, 0x0de0b6b3a7640000);
      var s13 := Dup(s12, 2);
      var s14 := Dup(s13, 2);
      var s15 := Dup(s14, 4);
      var s16 := Add(s15);
      var s17 := Lt(s16);
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s19, gas - 1)
      else
        ExecuteFromCFGNode_s272(s19, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 181
    * Starting at 0xda3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x03a0);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x0360);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 2, 0x03a0);
      var s13 := MLoad(s12);
      var s14 := Gt(s13);
      var s15 := PushN(s14, 2, 0x0deb);
      assert s15.stack[0] == 0xdeb;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s318(s16, gas - 1)
      else
        ExecuteFromCFGNode_s273(s16, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 182
    * Starting at 0xdbb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0360);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x03a0);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Lt(s6);
      var s8 := PushN(s7, 2, 0x1a5b);
      assert s8.stack[0] == 0x1a5b;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s9, gas - 1)
      else
        ExecuteFromCFGNode_s274(s9, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 183
    * Starting at 0xdca
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s8 := PushN(s7, 1, 0x01);
      var s9 := Dup(s8, 2);
      var s10 := Dup(s9, 2);
      var s11 := Dup(s10, 4);
      var s12 := Add(s11);
      var s13 := Lt(s12);
      var s14 := PushN(s13, 2, 0x1a5b);
      assert s14.stack[0] == 0x1a5b;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s15, gas - 1)
      else
        ExecuteFromCFGNode_s275(s15, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 184
    * Starting at 0xddc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xddc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x03a0);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x0e18);
      assert s10.stack[0] == 0xe18;
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s11, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 188
    * Starting at 0xe18
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 8, 0x0de0b6b3a7640000);
      var s3 := PushN(s2, 1, 0xa4);
      var s4 := CallDataLoad(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Mul(s6);
      var s8 := Dup(s7, 3);
      var s9 := IsZero(s8);
      var s10 := Dup(s9, 3);
      var s11 := Dup(s10, 5);
      var s12 := Dup(s11, 4);
      var s13 := Div(s12);
      var s14 := Eq(s13);
      var s15 := Or(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x1a5b);
      assert s17.stack[0] == 0x1a5b;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s18, gas - 1)
      else
        ExecuteFromCFGNode_s277(s18, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 189
    * Starting at 0xe35
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x24);
      var s6 := CallDataLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s278(s11, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 190
    * Starting at 0xe43
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x03a0);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := Dup(s9, 3);
      var s11 := Mul(s10);
      var s12 := Dup(s11, 3);
      var s13 := IsZero(s12);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := Dup(s15, 4);
      var s17 := Div(s16);
      var s18 := Eq(s17);
      var s19 := Or(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x1a5b);
      assert s21.stack[0] == 0x1a5b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s22, gas - 1)
      else
        ExecuteFromCFGNode_s279(s22, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 191
    * Starting at 0xe5d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x24);
      var s6 := CallDataLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s280(s11, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 192
    * Starting at 0xe6b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x03a0);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := Dup(s9, 3);
      var s11 := Mul(s10);
      var s12 := Dup(s11, 3);
      var s13 := IsZero(s12);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := Dup(s15, 4);
      var s17 := Div(s16);
      var s18 := Eq(s17);
      var s19 := Or(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x1a5b);
      assert s21.stack[0] == 0x1a5b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s22, gas - 1)
      else
        ExecuteFromCFGNode_s281(s22, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 193
    * Starting at 0xe85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x2710);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Mul(s7);
      var s9 := Dup(s8, 3);
      var s10 := IsZero(s9);
      var s11 := Dup(s10, 3);
      var s12 := Dup(s11, 5);
      var s13 := Dup(s12, 4);
      var s14 := Div(s13);
      var s15 := Eq(s14);
      var s16 := Or(s15);
      var s17 := IsZero(s16);
      var s18 := PushN(s17, 2, 0x1a5b);
      assert s18.stack[0] == 0x1a5b;
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s19, gas - 1)
      else
        ExecuteFromCFGNode_s282(s19, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 194
    * Starting at 0xe9c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0x04);
      var s6 := CallDataLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s283(s11, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 195
    * Starting at 0xeaa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x03c0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 8, 0x0de0b6b3a7640000);
      var s10 := PushN(s9, 8, 0x1bc16d674ec80000);
      var s11 := PushN(s10, 2, 0x0360);
      var s12 := MLoad(s11);
      var s13 := Dup(s12, 1);
      var s14 := Dup(s13, 3);
      var s15 := Mul(s14);
      var s16 := Dup(s15, 3);
      var s17 := IsZero(s16);
      var s18 := Dup(s17, 3);
      var s19 := Dup(s18, 5);
      var s20 := Dup(s19, 4);
      var s21 := Div(s20);
      var s22 := Eq(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := PushN(s24, 2, 0x1a5b);
      assert s25.stack[0] == 0x1a5b;
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s26, gas - 1)
      else
        ExecuteFromCFGNode_s284(s26, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 196
    * Starting at 0xeda
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x03a0);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s11, gas - 1)
      else
        ExecuteFromCFGNode_s285(s11, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 197
    * Starting at 0xee9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := Dup(s6, 2);
      var s8 := Dup(s7, 2);
      var s9 := Dup(s8, 4);
      var s10 := Add(s9);
      var s11 := Lt(s10);
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s13, gas - 1)
      else
        ExecuteFromCFGNode_s286(s13, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 198
    * Starting at 0xef8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x03e0);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 8, 0x0de0b6b3a7640000);
      var s11 := PushN(s10, 2, 0x0240);
      var s12 := MLoad(s11);
      var s13 := Dup(s12, 1);
      var s14 := Dup(s13, 3);
      var s15 := Mul(s14);
      var s16 := Dup(s15, 3);
      var s17 := IsZero(s16);
      var s18 := Dup(s17, 3);
      var s19 := Dup(s18, 5);
      var s20 := Dup(s19, 4);
      var s21 := Div(s20);
      var s22 := Eq(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := PushN(s24, 2, 0x1a5b);
      assert s25.stack[0] == 0x1a5b;
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s26, gas - 1)
      else
        ExecuteFromCFGNode_s287(s26, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 199
    * Starting at 0xf20
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0380);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x03e0);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := Dup(s9, 3);
      var s11 := Mul(s10);
      var s12 := Dup(s11, 3);
      var s13 := IsZero(s12);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := Dup(s15, 4);
      var s17 := Div(s16);
      var s18 := Eq(s17);
      var s19 := Or(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x1a5b);
      assert s21.stack[0] == 0x1a5b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s22, gas - 1)
      else
        ExecuteFromCFGNode_s288(s22, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 200
    * Starting at 0xf3c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := Dup(s6, 4);
      var s8 := Add(s7);
      var s9 := Lt(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s11, gas - 1)
      else
        ExecuteFromCFGNode_s289(s11, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 201
    * Starting at 0xf49
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x03c0);
      var s9 := MLoad(s8);
      var s10 := Dup(s9, 2);
      var s11 := Dup(s10, 2);
      var s12 := Dup(s11, 4);
      var s13 := Add(s12);
      var s14 := Lt(s13);
      var s15 := PushN(s14, 2, 0x1a5b);
      assert s15.stack[0] == 0x1a5b;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s16, gas - 1)
      else
        ExecuteFromCFGNode_s290(s16, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 202
    * Starting at 0xf5d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0400);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0xa4);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 2, 0x03e0);
      var s13 := MLoad(s12);
      var s14 := Dup(s13, 1);
      var s15 := Dup(s14, 3);
      var s16 := Mul(s15);
      var s17 := Dup(s16, 3);
      var s18 := IsZero(s17);
      var s19 := Dup(s18, 3);
      var s20 := Dup(s19, 5);
      var s21 := Dup(s20, 4);
      var s22 := Div(s21);
      var s23 := Eq(s22);
      var s24 := Or(s23);
      var s25 := IsZero(s24);
      var s26 := PushN(s25, 2, 0x1a5b);
      assert s26.stack[0] == 0x1a5b;
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s27, gas - 1)
      else
        ExecuteFromCFGNode_s291(s27, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 203
    * Starting at 0xf7f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0420);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x0420);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 2, 0x0400);
      var s10 := MLoad(s9);
      var s11 := Lt(s10);
      var s12 := PushN(s11, 2, 0x0fb2);
      assert s12.stack[0] == 0xfb2;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s314(s13, gas - 1)
      else
        ExecuteFromCFGNode_s292(s13, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 204
    * Starting at 0xf94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0400);
      var s2 := Dup(s1, 1);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0420);
      var s5 := MLoad(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Lt(s7);
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s10, gas - 1)
      else
        ExecuteFromCFGNode_s293(s10, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 205
    * Starting at 0xfa4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa4 as nat
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
      var s8 := Dup(s7, 2);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      var s11 := PushN(s10, 2, 0x0fc8);
      assert s11.stack[0] == 0xfc8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s294(s12, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 207
    * Starting at 0xfc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0400);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0240);
      var s5 := MLoad(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 1);
      var s8 := IsZero(s7);
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s10, gas - 1)
      else
        ExecuteFromCFGNode_s295(s10, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 208
    * Starting at 0xfd8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0440);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x03c0);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x0440);
      var s12 := MLoad(s11);
      var s13 := Dup(s12, 1);
      var s14 := Dup(s13, 1);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x1a5b);
      assert s16.stack[0] == 0x1a5b;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s17, gas - 1)
      else
        ExecuteFromCFGNode_s296(s17, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 209
    * Starting at 0xff1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0460);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0400);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 8, 0x0de0b6b3a7640000);
      var s12 := PushN(s11, 1, 0xa4);
      var s13 := CallDataLoad(s12);
      var s14 := Dup(s13, 1);
      var s15 := Dup(s14, 3);
      var s16 := Mul(s15);
      var s17 := Dup(s16, 3);
      var s18 := IsZero(s17);
      var s19 := Dup(s18, 3);
      var s20 := Dup(s19, 5);
      var s21 := Dup(s20, 4);
      var s22 := Div(s21);
      var s23 := Eq(s22);
      var s24 := Or(s23);
      var s25 := IsZero(s24);
      var s26 := PushN(s25, 2, 0x1a5b);
      assert s26.stack[0] == 0x1a5b;
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s27, gas - 1)
      else
        ExecuteFromCFGNode_s297(s27, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 210
    * Starting at 0x101b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := Dup(s6, 4);
      var s8 := Add(s7);
      var s9 := Lt(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s11, gas - 1)
      else
        ExecuteFromCFGNode_s298(s11, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 211
    * Starting at 0x1028
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1028 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0440);
      var s9 := MLoad(s8);
      var s10 := Dup(s9, 1);
      var s11 := Dup(s10, 1);
      var s12 := IsZero(s11);
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s14, gas - 1)
      else
        ExecuteFromCFGNode_s299(s14, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 212
    * Starting at 0x103a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0460);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 8, 0x0de0b6b3a7640000);
      var s10 := Dup(s9, 1);
      var s11 := Dup(s10, 3);
      var s12 := Mul(s11);
      var s13 := Dup(s12, 3);
      var s14 := IsZero(s13);
      var s15 := Dup(s14, 3);
      var s16 := Dup(s15, 5);
      var s17 := Dup(s16, 4);
      var s18 := Div(s17);
      var s19 := Eq(s18);
      var s20 := Or(s19);
      var s21 := IsZero(s20);
      var s22 := PushN(s21, 2, 0x1a5b);
      assert s22.stack[0] == 0x1a5b;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s23, gas - 1)
      else
        ExecuteFromCFGNode_s300(s23, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 213
    * Starting at 0x105d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0360);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s11, gas - 1)
      else
        ExecuteFromCFGNode_s301(s11, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 214
    * Starting at 0x106c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := Dup(s6, 2);
      var s8 := Dup(s7, 2);
      var s9 := Dup(s8, 4);
      var s10 := Add(s9);
      var s11 := Lt(s10);
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s13, gas - 1)
      else
        ExecuteFromCFGNode_s302(s13, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 215
    * Starting at 0x107b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x0480);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x0460);
      var s11 := Dup(s10, 1);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 8, 0x0de0b6b3a7640000);
      var s14 := PushN(s13, 2, 0x0380);
      var s15 := MLoad(s14);
      var s16 := Dup(s15, 1);
      var s17 := Dup(s16, 3);
      var s18 := Mul(s17);
      var s19 := Dup(s18, 3);
      var s20 := IsZero(s19);
      var s21 := Dup(s20, 3);
      var s22 := Dup(s21, 5);
      var s23 := Dup(s22, 4);
      var s24 := Div(s23);
      var s25 := Eq(s24);
      var s26 := Or(s25);
      var s27 := IsZero(s26);
      var s28 := PushN(s27, 2, 0x1a5b);
      assert s28.stack[0] == 0x1a5b;
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s29, gas - 1)
      else
        ExecuteFromCFGNode_s303(s29, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 216
    * Starting at 0x10a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x0440);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s11, gas - 1)
      else
        ExecuteFromCFGNode_s304(s11, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 217
    * Starting at 0x10b7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := Dup(s6, 2);
      var s8 := Dup(s7, 2);
      var s9 := Dup(s8, 4);
      var s10 := Add(s9);
      var s11 := Lt(s10);
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s13, gas - 1)
      else
        ExecuteFromCFGNode_s305(s13, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 218
    * Starting at 0x10c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := Dup(s7, 2);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      var s11 := PushN(s10, 2, 0x0460);
      var s12 := MLoad(s11);
      var s13 := PushN(s12, 2, 0x0480);
      var s14 := MLoad(s13);
      var s15 := Lt(s14);
      var s16 := PushN(s15, 2, 0x10fb);
      assert s16.stack[0] == 0x10fb;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s313(s17, gas - 1)
      else
        ExecuteFromCFGNode_s306(s17, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 219
    * Starting at 0x10dd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0480);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0460);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Lt(s6);
      var s8 := PushN(s7, 2, 0x1a5b);
      assert s8.stack[0] == 0x1a5b;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s9, gas - 1)
      else
        ExecuteFromCFGNode_s307(s9, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 220
    * Starting at 0x10ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s8 := PushN(s7, 2, 0x0240);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x110d);
      assert s10.stack[0] == 0x110d;
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s11, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 222
    * Starting at 0x110d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 2, 0x04a0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x0340);
      var s6 := MLoad(s5);
      var s7 := PushN(s6, 2, 0x0240);
      var s8 := MLoad(s7);
      var s9 := Gt(s8);
      var s10 := PushN(s9, 2, 0x113f);
      assert s10.stack[0] == 0x113f;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s311(s11, gas - 1)
      else
        ExecuteFromCFGNode_s309(s11, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 223
    * Starting at 0x1121
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1121 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0340);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0240);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Lt(s6);
      var s8 := PushN(s7, 2, 0x1a5b);
      assert s8.stack[0] == 0x1a5b;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s9, gas - 1)
      else
        ExecuteFromCFGNode_s310(s9, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 224
    * Starting at 0x1130
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1130 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s8 := PushN(s7, 2, 0x04a0);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x115a);
      assert s10.stack[0] == 0x115a;
      var s11 := Jump(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 311
    * Segment Id for this node is: 225
    * Starting at 0x113f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0240);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0340);
      var s5 := MLoad(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Lt(s7);
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s10, gas - 1)
      else
        ExecuteFromCFGNode_s312(s10, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 226
    * Starting at 0x114f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s8 := PushN(s7, 2, 0x04a0);
      var s9 := MStore(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 313
    * Segment Id for this node is: 221
    * Starting at 0x10fb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0340);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x02);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Div(s6);
      var s8 := Swap(s7, 1);
      var s9 := Pop(s8);
      var s10 := Swap(s9, 1);
      var s11 := Pop(s10);
      var s12 := PushN(s11, 2, 0x0240);
      var s13 := MStore(s12);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s308(s13, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 206
    * Starting at 0xfb2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0340);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x02);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Div(s6);
      var s8 := Swap(s7, 1);
      var s9 := Pop(s8);
      var s10 := Swap(s9, 1);
      var s11 := Pop(s10);
      var s12 := PushN(s11, 2, 0x0240);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 2, 0x1204);
      assert s14.stack[0] == 0x1204;
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s15, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 238
    * Starting at 0x1204
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1204 as nat
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
      var s12 := PushN(s11, 2, 0x0d23);
      assert s12.stack[0] == 0xd23;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s13, gas - 1)
      else
        ExecuteFromCFGNode_s316(s13, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 239
    * Starting at 0x1214
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1214 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x10);
      var s4 := PushN(s3, 2, 0x0320);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 32, 0x446964206e6f7420636f6e766572676500000000000000000000000000000000);
      var s7 := PushN(s6, 2, 0x0340);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0320);
      var s10 := Pop(s9);
      var s11 := PushN(s10, 2, 0x0320);
      var s12 := MLoad(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x0340);
      var s15 := Add(s14);
      var s16 := Dup(s15, 2);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := PushN(s18, 1, 0x01);
      var s20 := Dup(s19, 3);
      var s21 := Sub(s20);
      var s22 := Mod(s21);
      var s23 := PushN(s22, 1, 0x1f);
      var s24 := Dup(s23, 3);
      var s25 := Add(s24);
      var s26 := Sub(s25);
      var s27 := Swap(s26, 1);
      var s28 := Pop(s27);
      var s29 := Sub(s28);
      var s30 := CallDataSize(s29);
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s317(s31, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 240
    * Starting at 0x1261
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1261 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataCopy(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := PushN(s3, 4, 0x08c379a0);
      var s5 := PushN(s4, 2, 0x02e0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 2, 0x0300);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x0320);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := PushN(s12, 1, 0x01);
      var s14 := Dup(s13, 3);
      var s15 := Sub(s14);
      var s16 := Mod(s15);
      var s17 := PushN(s16, 1, 0x1f);
      var s18 := Dup(s17, 3);
      var s19 := Add(s18);
      var s20 := Sub(s19);
      var s21 := Swap(s20, 1);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x44);
      var s24 := Add(s23);
      var s25 := PushN(s24, 2, 0x02fc);
      var s26 := Revert(s25);
      // Segment is terminal (Revert, Stop or Return)
      s26
  }

  /** Node 318
    * Segment Id for this node is: 185
    * Starting at 0xdeb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdeb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x03a0);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0360);
      var s5 := MLoad(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Lt(s7);
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s10, gas - 1)
      else
        ExecuteFromCFGNode_s319(s10, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 186
    * Starting at 0xdfb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s8 := PushN(s7, 1, 0x01);
      var s9 := Dup(s8, 2);
      var s10 := Dup(s9, 2);
      var s11 := Dup(s10, 4);
      var s12 := Add(s11);
      var s13 := Lt(s12);
      var s14 := PushN(s13, 2, 0x1a5b);
      assert s14.stack[0] == 0x1a5b;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s15, gas - 1)
      else
        ExecuteFromCFGNode_s320(s15, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 187
    * Starting at 0xe0d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 2, 0x03a0);
      var s9 := MStore(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s276(s9, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 160
    * Starting at 0xbf1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s252(s2, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 157
    * Starting at 0xbdc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s250(s2, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0xb90;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[7] == 0xb90;
      var s3 := Dup(s2, 1);
      assert s3.stack[8] == 0xb90;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 324
    * Segment Id for this node is: 297
    * Starting at 0x1772
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1772 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0xb90;
      var s2 := PushN(s1, 2, 0x0220);
      assert s2.stack[6] == 0xb90;
      var s3 := MLoad(s2);
      assert s3.stack[6] == 0xb90;
      var s4 := PushN(s3, 2, 0x0140);
      assert s4.stack[7] == 0xb90;
      var s5 := PushN(s4, 2, 0x01e0);
      assert s5.stack[8] == 0xb90;
      var s6 := MLoad(s5);
      assert s6.stack[8] == 0xb90;
      var s7 := PushN(s6, 1, 0x03);
      assert s7.stack[9] == 0xb90;
      var s8 := Dup(s7, 2);
      assert s8.stack[10] == 0xb90;
      var s9 := Lt(s8);
      assert s9.stack[9] == 0xb90;
      var s10 := IsZero(s9);
      assert s10.stack[9] == 0xb90;
      var s11 := PushN(s10, 2, 0x1a5b);
      assert s11.stack[0] == 0x1a5b;
      assert s11.stack[10] == 0xb90;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s329(s12, gas - 1)
      else
        ExecuteFromCFGNode_s325(s12, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 298
    * Starting at 0x1787
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1787 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[9] == 0xb90;
      var s2 := Mul(s1);
      assert s2.stack[8] == 0xb90;
      var s3 := Add(s2);
      assert s3.stack[7] == 0xb90;
      var s4 := MStore(s3);
      assert s4.stack[5] == 0xb90;
      var s5 := PushN(s4, 2, 0x01e0);
      assert s5.stack[6] == 0xb90;
      var s6 := Dup(s5, 1);
      assert s6.stack[7] == 0xb90;
      var s7 := MLoad(s6);
      assert s7.stack[7] == 0xb90;
      var s8 := PushN(s7, 1, 0x01);
      assert s8.stack[8] == 0xb90;
      var s9 := Dup(s8, 1);
      assert s9.stack[9] == 0xb90;
      var s10 := Dup(s9, 3);
      assert s10.stack[10] == 0xb90;
      var s11 := Lt(s10);
      assert s11.stack[9] == 0xb90;
      var s12 := PushN(s11, 2, 0x1a5b);
      assert s12.stack[0] == 0x1a5b;
      assert s12.stack[10] == 0xb90;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s329(s13, gas - 1)
      else
        ExecuteFromCFGNode_s326(s13, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 299
    * Starting at 0x179a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x179a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[9] == 0xb90;
      var s2 := Dup(s1, 3);
      assert s2.stack[10] == 0xb90;
      var s3 := Sub(s2);
      assert s3.stack[9] == 0xb90;
      var s4 := Swap(s3, 1);
      assert s4.stack[9] == 0xb90;
      var s5 := Pop(s4);
      assert s5.stack[8] == 0xb90;
      var s6 := Swap(s5, 1);
      assert s6.stack[8] == 0xb90;
      var s7 := Pop(s6);
      assert s7.stack[7] == 0xb90;
      var s8 := Dup(s7, 2);
      assert s8.stack[8] == 0xb90;
      var s9 := MStore(s8);
      assert s9.stack[6] == 0xb90;
      var s10 := Pop(s9);
      assert s10.stack[5] == 0xb90;
      var s11 := PushN(s10, 2, 0x01e0);
      assert s11.stack[6] == 0xb90;
      var s12 := MLoad(s11);
      assert s12.stack[6] == 0xb90;
      var s13 := PushN(s12, 2, 0x17b0);
      assert s13.stack[0] == 0x17b0;
      assert s13.stack[7] == 0xb90;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s328(s14, gas - 1)
      else
        ExecuteFromCFGNode_s327(s14, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 300
    * Starting at 0x17ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x17c0);
      assert s1.stack[0] == 0x17c0;
      assert s1.stack[6] == 0xb90;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s2, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 301
    * Starting at 0x17b0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0xb90;
      var s2 := Dup(s1, 2);
      assert s2.stack[6] == 0xb90;
      var s3 := MLoad(s2);
      assert s3.stack[6] == 0xb90;
      var s4 := PushN(s3, 1, 0x01);
      assert s4.stack[7] == 0xb90;
      var s5 := Add(s4);
      assert s5.stack[6] == 0xb90;
      var s6 := Dup(s5, 1);
      assert s6.stack[7] == 0xb90;
      var s7 := Dup(s6, 4);
      assert s7.stack[8] == 0xb90;
      var s8 := MStore(s7);
      assert s8.stack[6] == 0xb90;
      var s9 := Dup(s8, 2);
      assert s9.stack[7] == 0xb90;
      var s10 := Eq(s9);
      assert s10.stack[6] == 0xb90;
      var s11 := IsZero(s10);
      assert s11.stack[6] == 0xb90;
      var s12 := PushN(s11, 2, 0x1736);
      assert s12.stack[0] == 0x1736;
      assert s12.stack[7] == 0xb90;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s13, gas - 1)
      else
        ExecuteFromCFGNode_s244(s13, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0xb90;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[9] == 0xb90;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0xb90;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 330
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0xb90;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[8] == 0xb90;
      var s3 := Dup(s2, 1);
      assert s3.stack[9] == 0xb90;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 331
    * Segment Id for this node is: 330
    * Starting at 0x1a5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xb90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0xb90;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[6] == 0xb90;
      var s3 := Dup(s2, 1);
      assert s3.stack[7] == 0xb90;
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 332
    * Segment Id for this node is: 148
    * Starting at 0xaf9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 9, 0x056bc75e2d63100001);
      var s3 := PushN(s2, 2, 0x0260);
      var s4 := MLoad(s3);
      var s5 := Lt(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s232(s5, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 140
    * Starting at 0xa74
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 14, 0x314dc6448d9338c15b0a00000001);
      var s3 := PushN(s2, 1, 0xa4);
      var s4 := CallDataLoad(s3);
      var s5 := Lt(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s225(s5, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 136
    * Starting at 0xa4a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 7, 0xb1a2bc2ec50001);
      var s3 := PushN(s2, 1, 0x24);
      var s4 := CallDataLoad(s3);
      var s5 := Lt(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s222(s5, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 132
    * Starting at 0xa26
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x1017df81);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := CallDataLoad(s3);
      var s5 := Lt(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s219(s5, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 242
    * Starting at 0x128e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x571bae3f);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x1583);
      assert s5.stack[0] == 0x1583;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s369(s6, gas - 1)
      else
        ExecuteFromCFGNode_s337(s6, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 243
    * Starting at 0x129a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 8, 0x0de0b6b3a7640000);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := Div(s5);
      var s7 := Swap(s6, 1);
      var s8 := Pop(s7);
      var s9 := Swap(s8, 1);
      var s10 := Pop(s9);
      var s11 := PushN(s10, 1, 0xe0);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 1, 0x04);
      var s14 := CallDataLoad(s13);
      var s15 := PushN(s14, 1, 0xe0);
      var s16 := MLoad(s15);
      var s17 := PushN(s16, 8, 0x0de0b6b3a7640000);
      var s18 := Dup(s17, 1);
      var s19 := Dup(s18, 3);
      var s20 := Mul(s19);
      var s21 := Dup(s20, 3);
      var s22 := IsZero(s21);
      var s23 := Dup(s22, 3);
      var s24 := Dup(s23, 5);
      var s25 := Dup(s24, 4);
      var s26 := Div(s25);
      var s27 := Eq(s26);
      var s28 := Or(s27);
      var s29 := IsZero(s28);
      var s30 := PushN(s29, 2, 0x1a5b);
      assert s30.stack[0] == 0x1a5b;
      var s31 := JumpI(s30);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s30.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s31, gas - 1)
      else
        ExecuteFromCFGNode_s338(s31, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 244
    * Starting at 0x12cf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Lt(s6);
      var s8 := PushN(s7, 2, 0x1a5b);
      assert s8.stack[0] == 0x1a5b;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s9, gas - 1)
      else
        ExecuteFromCFGNode_s339(s9, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 245
    * Starting at 0x12da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12da as nat
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
      var s10 := PushN(s9, 1, 0x3b);
      var s11 := PushN(s10, 1, 0xe0);
      var s12 := MLoad(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := PushN(s14, 2, 0x12ff);
      assert s15.stack[0] == 0x12ff;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s342(s16, gas - 1)
      else
        ExecuteFromCFGNode_s340(s16, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 246
    * Starting at 0x12f0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 2, 0x0120);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 1, 0x20);
      var s5 := PushN(s4, 2, 0x0120);
      var s6 := PushN(s5, 2, 0x1581);
      assert s6.stack[0] == 0x1581;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s7, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 273
    * Starting at 0x1581
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1581 as nat
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

  /** Node 342
    * Segment Id for this node is: 247
    * Starting at 0x12ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 8, 0x0de0b6b3a7640000);
      var s3 := PushN(s2, 2, 0x0100);
      var s4 := PushN(s3, 1, 0xe0);
      var s5 := MLoad(s4);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x1a5b);
      assert s8.stack[0] == 0x1a5b;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s9, gas - 1)
      else
        ExecuteFromCFGNode_s343(s9, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 248
    * Starting at 0x1315
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1315 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 1, 0x02);
      var s4 := Exp(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 1);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x1a5b);
      assert s8.stack[0] == 0x1a5b;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s9, gas - 1)
      else
        ExecuteFromCFGNode_s344(s9, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 249
    * Starting at 0x1322
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1322 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0120);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0100);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x1345);
      assert s11.stack[0] == 0x1345;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s346(s12, gas - 1)
      else
        ExecuteFromCFGNode_s345(s12, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 250
    * Starting at 0x1334
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1334 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0120);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 2, 0x0140);
      var s7 := PushN(s6, 2, 0x1581);
      assert s7.stack[0] == 0x1581;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s8, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 251
    * Starting at 0x1345
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1345 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 8, 0x0de0b6b3a7640000);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 8, 0x06f05b59d3b20000);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 8, 0x0de0b6b3a7640000);
      var s9 := PushN(s8, 2, 0x0180);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x00);
      var s12 := PushN(s11, 2, 0x01a0);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 2, 0x01c0);
      var s15 := PushN(s14, 1, 0x01);
      var s16 := PushN(s15, 1, 0xff);
      var s17 := Dup(s16, 2);
      var s18 := Dup(s17, 4);
      var s19 := MStore(s18);
      var s20 := Add(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s347(s20, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 252
    * Starting at 0x137e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x137e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x01c0);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 8, 0x0de0b6b3a7640000);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Mul(s6);
      var s8 := Dup(s7, 3);
      var s9 := IsZero(s8);
      var s10 := Dup(s9, 3);
      var s11 := Dup(s10, 5);
      var s12 := Dup(s11, 4);
      var s13 := Div(s12);
      var s14 := Eq(s13);
      var s15 := Or(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x1a5b);
      assert s17.stack[0] == 0x1a5b;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s18, gas - 1)
      else
        ExecuteFromCFGNode_s348(s18, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 253
    * Starting at 0x139c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x01e0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 2, 0x01e0);
      var s8 := MLoad(s7);
      var s9 := PushN(s8, 8, 0x0de0b6b3a7640000);
      var s10 := Dup(s9, 1);
      var s11 := Dup(s10, 3);
      var s12 := Lt(s11);
      var s13 := PushN(s12, 2, 0x1a5b);
      assert s13.stack[0] == 0x1a5b;
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s14, gas - 1)
      else
        ExecuteFromCFGNode_s349(s14, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 254
    * Starting at 0x13b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s10 := PushN(s9, 2, 0x0200);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 2, 0x0100);
      var s13 := MLoad(s12);
      var s14 := Gt(s13);
      var s15 := PushN(s14, 2, 0x13ee);
      assert s15.stack[0] == 0x13ee;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s367(s16, gas - 1)
      else
        ExecuteFromCFGNode_s350(s16, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 255
    * Starting at 0x13d0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0200);
      var s2 := Dup(s1, 1);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MLoad(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Lt(s7);
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s10, gas - 1)
      else
        ExecuteFromCFGNode_s351(s10, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 256
    * Starting at 0x13e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e0 as nat
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
      var s8 := Dup(s7, 2);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      var s11 := PushN(s10, 2, 0x1412);
      assert s11.stack[0] == 0x1412;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s12, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 259
    * Starting at 0x1412
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1412 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0140);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0200);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MLoad(s6);
      var s8 := Dup(s7, 1);
      var s9 := Dup(s8, 3);
      var s10 := Mul(s9);
      var s11 := Dup(s10, 3);
      var s12 := IsZero(s11);
      var s13 := Dup(s12, 3);
      var s14 := Dup(s13, 5);
      var s15 := Dup(s14, 4);
      var s16 := Div(s15);
      var s17 := Eq(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := PushN(s19, 2, 0x1a5b);
      assert s20.stack[0] == 0x1a5b;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s21, gas - 1)
      else
        ExecuteFromCFGNode_s353(s21, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 260
    * Starting at 0x142f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x142f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 8, 0x0de0b6b3a7640000);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Div(s7);
      var s9 := Swap(s8, 1);
      var s10 := Pop(s9);
      var s11 := Swap(s10, 1);
      var s12 := Pop(s11);
      var s13 := Dup(s12, 1);
      var s14 := Dup(s13, 3);
      var s15 := Mul(s14);
      var s16 := Dup(s15, 3);
      var s17 := IsZero(s16);
      var s18 := Dup(s17, 3);
      var s19 := Dup(s18, 5);
      var s20 := Dup(s19, 4);
      var s21 := Div(s20);
      var s22 := Eq(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := PushN(s24, 2, 0x1a5b);
      assert s25.stack[0] == 0x1a5b;
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s26, gas - 1)
      else
        ExecuteFromCFGNode_s354(s26, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 261
    * Starting at 0x1453
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1453 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 2, 0x01e0);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s355(s11, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 262
    * Starting at 0x1462
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1462 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 2, 0x0140);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x01a0);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x1494);
      assert s11.stack[0] == 0x1494;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s365(s12, gas - 1)
      else
        ExecuteFromCFGNode_s356(s12, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 263
    * Starting at 0x1474
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1474 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0180);
      var s2 := Dup(s1, 1);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0140);
      var s5 := MLoad(s4);
      var s6 := Dup(s5, 2);
      var s7 := Dup(s6, 2);
      var s8 := Dup(s7, 4);
      var s9 := Add(s8);
      var s10 := Lt(s9);
      var s11 := PushN(s10, 2, 0x1a5b);
      assert s11.stack[0] == 0x1a5b;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s12, gas - 1)
      else
        ExecuteFromCFGNode_s357(s12, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 264
    * Starting at 0x1486
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1486 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := Dup(s7, 2);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      var s11 := PushN(s10, 2, 0x14af);
      assert s11.stack[0] == 0x14af;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s358(s12, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 267
    * Starting at 0x14af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x24);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 2, 0x0140);
      var s5 := MLoad(s4);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x14f9);
      assert s8.stack[0] == 0x14f9;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s362(s9, gas - 1)
      else
        ExecuteFromCFGNode_s359(s9, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 268
    * Starting at 0x14bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := PushN(s3, 2, 0x0120);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 2, 0x0180);
      var s7 := MLoad(s6);
      var s8 := Dup(s7, 1);
      var s9 := Dup(s8, 3);
      var s10 := Mul(s9);
      var s11 := Dup(s10, 3);
      var s12 := IsZero(s11);
      var s13 := Dup(s12, 3);
      var s14 := Dup(s13, 5);
      var s15 := Dup(s14, 4);
      var s16 := Div(s15);
      var s17 := Eq(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := PushN(s19, 2, 0x1a5b);
      assert s20.stack[0] == 0x1a5b;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s21, gas - 1)
      else
        ExecuteFromCFGNode_s360(s21, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 269
    * Starting at 0x14d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 8, 0x0de0b6b3a7640000);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Div(s7);
      var s9 := Swap(s8, 1);
      var s10 := Pop(s9);
      var s11 := Swap(s10, 1);
      var s12 := Pop(s11);
      var s13 := PushN(s12, 2, 0x0220);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 1, 0x20);
      var s16 := PushN(s15, 2, 0x0220);
      var s17 := PushN(s16, 2, 0x1581);
      assert s17.stack[0] == 0x1581;
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s361(s18, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 273
    * Starting at 0x1581
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1581 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Return(s1);
      // Segment is terminal (Revert, Stop or Return)
      s2
  }

  /** Node 362
    * Segment Id for this node is: 270
    * Starting at 0x14f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f9 as nat
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
      var s12 := PushN(s11, 2, 0x137e);
      assert s12.stack[0] == 0x137e;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s347(s13, gas - 1)
      else
        ExecuteFromCFGNode_s363(s13, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 271
    * Starting at 0x1509
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1509 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x10);
      var s4 := PushN(s3, 2, 0x01c0);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 32, 0x446964206e6f7420636f6e766572676500000000000000000000000000000000);
      var s7 := PushN(s6, 2, 0x01e0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x01c0);
      var s10 := Pop(s9);
      var s11 := PushN(s10, 2, 0x01c0);
      var s12 := MLoad(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x01e0);
      var s15 := Add(s14);
      var s16 := Dup(s15, 2);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := PushN(s18, 1, 0x01);
      var s20 := Dup(s19, 3);
      var s21 := Sub(s20);
      var s22 := Mod(s21);
      var s23 := PushN(s22, 1, 0x1f);
      var s24 := Dup(s23, 3);
      var s25 := Add(s24);
      var s26 := Sub(s25);
      var s27 := Swap(s26, 1);
      var s28 := Pop(s27);
      var s29 := Sub(s28);
      var s30 := CallDataSize(s29);
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s364(s31, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 272
    * Starting at 0x1556
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1556 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataCopy(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := PushN(s3, 4, 0x08c379a0);
      var s5 := PushN(s4, 2, 0x0180);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 2, 0x01a0);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x01c0);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := PushN(s12, 1, 0x01);
      var s14 := Dup(s13, 3);
      var s15 := Sub(s14);
      var s16 := Mod(s15);
      var s17 := PushN(s16, 1, 0x1f);
      var s18 := Dup(s17, 3);
      var s19 := Add(s18);
      var s20 := Sub(s19);
      var s21 := Swap(s20, 1);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x44);
      var s24 := Add(s23);
      var s25 := PushN(s24, 2, 0x019c);
      var s26 := Revert(s25);
      // Segment is terminal (Revert, Stop or Return)
      s26
  }

  /** Node 365
    * Segment Id for this node is: 265
    * Starting at 0x1494
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1494 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0180);
      var s3 := Dup(s2, 1);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 2, 0x0140);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 3);
      var s9 := Lt(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s366(s11, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 266
    * Starting at 0x14a5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a5 as nat
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
      var s8 := Dup(s7, 2);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s358(s10, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 257
    * Starting at 0x13ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0100);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0200);
      var s5 := MLoad(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := Lt(s7);
      var s9 := PushN(s8, 2, 0x1a5b);
      assert s9.stack[0] == 0x1a5b;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s10, gas - 1)
      else
        ExecuteFromCFGNode_s368(s10, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 258
    * Starting at 0x13fe
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      var s10 := PushN(s9, 2, 0x01a0);
      var s11 := MLoad(s10);
      var s12 := IsZero(s11);
      var s13 := PushN(s12, 2, 0x01a0);
      var s14 := MStore(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s352(s14, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 274
    * Starting at 0x1583
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1583 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x4e60b141);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x16de);
      assert s5.stack[0] == 0x16de;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s384(s6, gas - 1)
      else
        ExecuteFromCFGNode_s370(s6, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 275
    * Starting at 0x158f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x158f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 2, 0x15a3);
      assert s3.stack[0] == 0x15a3;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s373(s4, gas - 1)
      else
        ExecuteFromCFGNode_s371(s4, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 276
    * Starting at 0x1596
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1596 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 1, 0x20);
      var s5 := PushN(s4, 1, 0xe0);
      var s6 := PushN(s5, 2, 0x16dc);
      assert s6.stack[0] == 0x16dc;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s7, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 287
    * Starting at 0x16dc
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16dc as nat
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

  /** Node 373
    * Segment Id for this node is: 277
    * Starting at 0x15a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 8, 0x0de0b6b3a7640000);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := Dup(s6, 4);
      var s8 := Add(s7);
      var s9 := Lt(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s11, gas - 1)
      else
        ExecuteFromCFGNode_s374(s11, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 278
    * Starting at 0x15b9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 1, 0x02);
      var s9 := Dup(s8, 1);
      var s10 := Dup(s9, 3);
      var s11 := Div(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := PushN(s15, 1, 0xe0);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 1, 0x04);
      var s19 := CallDataLoad(s18);
      var s20 := PushN(s19, 2, 0x0100);
      var s21 := MStore(s20);
      var s22 := PushN(s21, 2, 0x0120);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0100);
      var s25 := Dup(s24, 2);
      var s26 := Dup(s25, 4);
      var s27 := MStore(s26);
      var s28 := Add(s27);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s375(s28, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 279
    * Starting at 0x15df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0100);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0xe0);
      var s5 := MLoad(s4);
      var s6 := Xor(s5);
      var s7 := PushN(s6, 2, 0x1600);
      assert s7.stack[0] == 0x1600;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s378(s8, gas - 1)
      else
        ExecuteFromCFGNode_s376(s8, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 280
    * Starting at 0x15ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 2, 0x0140);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := PushN(s8, 2, 0x0140);
      var s10 := PushN(s9, 2, 0x16dc);
      assert s10.stack[0] == 0x16dc;
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s11, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 287
    * Starting at 0x16dc
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Return(s1);
      // Segment is terminal (Revert, Stop or Return)
      s2
  }

  /** Node 378
    * Segment Id for this node is: 281
    * Starting at 0x1600
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1600 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := CallDataLoad(s6);
      var s8 := PushN(s7, 8, 0x0de0b6b3a7640000);
      var s9 := Dup(s8, 1);
      var s10 := Dup(s9, 3);
      var s11 := Mul(s10);
      var s12 := Dup(s11, 3);
      var s13 := IsZero(s12);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := Dup(s15, 4);
      var s17 := Div(s16);
      var s18 := Eq(s17);
      var s19 := Or(s18);
      var s20 := IsZero(s19);
      var s21 := PushN(s20, 2, 0x1a5b);
      assert s21.stack[0] == 0x1a5b;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s22, gas - 1)
      else
        ExecuteFromCFGNode_s379(s22, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 282
    * Starting at 0x1624
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1624 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := PushN(s4, 1, 0xe0);
      var s6 := MLoad(s5);
      var s7 := Dup(s6, 1);
      var s8 := Dup(s7, 1);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x1a5b);
      assert s10.stack[0] == 0x1a5b;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s11, gas - 1)
      else
        ExecuteFromCFGNode_s380(s11, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 283
    * Starting at 0x1632
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1632 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      var s2 := Div(s1);
      var s3 := Swap(s2, 1);
      var s4 := Pop(s3);
      var s5 := Swap(s4, 1);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 1, 0xe0);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 2);
      var s10 := Dup(s9, 2);
      var s11 := Dup(s10, 4);
      var s12 := Add(s11);
      var s13 := Lt(s12);
      var s14 := PushN(s13, 2, 0x1a5b);
      assert s14.stack[0] == 0x1a5b;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s15, gas - 1)
      else
        ExecuteFromCFGNode_s381(s15, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 284
    * Starting at 0x1644
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1644 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Add(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := PushN(s7, 1, 0x02);
      var s9 := Dup(s8, 1);
      var s10 := Dup(s9, 3);
      var s11 := Div(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := PushN(s15, 1, 0xe0);
      var s17 := MStore(s16);
      var s18 := Dup(s17, 2);
      var s19 := MLoad(s18);
      var s20 := PushN(s19, 1, 0x01);
      var s21 := Add(s20);
      var s22 := Dup(s21, 1);
      var s23 := Dup(s22, 4);
      var s24 := MStore(s23);
      var s25 := Dup(s24, 2);
      var s26 := Eq(s25);
      var s27 := IsZero(s26);
      var s28 := PushN(s27, 2, 0x15df);
      assert s28.stack[0] == 0x15df;
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s375(s29, gas - 1)
      else
        ExecuteFromCFGNode_s382(s29, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 285
    * Starting at 0x1666
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1666 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 1, 0x10);
      var s4 := PushN(s3, 2, 0x0120);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 32, 0x446964206e6f7420636f6e766572676500000000000000000000000000000000);
      var s7 := PushN(s6, 2, 0x0140);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0120);
      var s10 := Pop(s9);
      var s11 := PushN(s10, 2, 0x0120);
      var s12 := MLoad(s11);
      var s13 := Dup(s12, 1);
      var s14 := PushN(s13, 2, 0x0140);
      var s15 := Add(s14);
      var s16 := Dup(s15, 2);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := PushN(s18, 1, 0x01);
      var s20 := Dup(s19, 3);
      var s21 := Sub(s20);
      var s22 := Mod(s21);
      var s23 := PushN(s22, 1, 0x1f);
      var s24 := Dup(s23, 3);
      var s25 := Add(s24);
      var s26 := Sub(s25);
      var s27 := Swap(s26, 1);
      var s28 := Pop(s27);
      var s29 := Sub(s28);
      var s30 := CallDataSize(s29);
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s383(s31, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 286
    * Starting at 0x16b3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataCopy(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := PushN(s3, 4, 0x08c379a0);
      var s5 := PushN(s4, 1, 0xe0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 2, 0x0100);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x0120);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := PushN(s12, 1, 0x01);
      var s14 := Dup(s13, 3);
      var s15 := Sub(s14);
      var s16 := Mod(s15);
      var s17 := PushN(s16, 1, 0x1f);
      var s18 := Dup(s17, 3);
      var s19 := Add(s18);
      var s20 := Sub(s19);
      var s21 := Swap(s20, 1);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x44);
      var s24 := Add(s23);
      var s25 := PushN(s24, 1, 0xfc);
      var s26 := Revert(s25);
      // Segment is terminal (Revert, Stop or Return)
      s26
  }

  /** Node 384
    * Segment Id for this node is: 288
    * Starting at 0x16de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16de as nat
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
