
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
      var s1 := PushN(s0, 1, 0x80);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 1, 0x04);
      var s5 := CallDataSize(s4);
      var s6 := Lt(s5);
      var s7 := PushN(s6, 2, 0x003f);
      assert s7.stack[0] == 0x3f;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s268(s8, gas - 1)
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
      var s1 := PushN(s0, 1, 0x00);
      var s2 := CallDataLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := Shr(s3);
      var s5 := Dup(s4, 1);
      var s6 := PushN(s5, 4, 0x01ffc9a7);
      var s7 := Eq(s6);
      var s8 := PushN(s7, 2, 0x0044);
      assert s8.stack[0] == 0x44;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s259(s9, gas - 1)
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
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x22895118);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x00a4);
      assert s4.stack[0] == 0xa4;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s5, gas - 1)
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
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x621fd130);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x01ba);
      assert s4.stack[0] == 0x1ba;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s5, gas - 1)
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
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0xc5f2892f);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x0244);
      assert s4.stack[0] == 0x244;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s6(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x3f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
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
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 6
    * Segment Id for this node is: 43
    * Starting at 0x244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup(s2, 1);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x0250);
      assert s5.stack[0] == 0x250;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s6, gas - 1)
      else
        ExecuteFromCFGNode_s7(s6, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 44
    * Starting at 0x24c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Dup(s1, 1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 8
    * Segment Id for this node is: 45
    * Starting at 0x250
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x250 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0259);
      assert s3.stack[0] == 0x259;
      var s4 := PushN(s3, 2, 0x10c7);
      assert s4.stack[0] == 0x10c7;
      assert s4.stack[1] == 0x259;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 183
    * Starting at 0x10c7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[1] == 0x259;
      var s3 := SLoad(s2);
      assert s3.stack[1] == 0x259;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[2] == 0x259;
      var s5 := Swap(s4, 1);
      assert s5.stack[2] == 0x259;
      var s6 := Dup(s5, 2);
      assert s6.stack[3] == 0x259;
      var s7 := Swap(s6, 1);
      assert s7.stack[3] == 0x259;
      var s8 := Dup(s7, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s10(s8, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 184
    * Starting at 0x10d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[5] == 0x259;
      var s3 := Dup(s2, 2);
      assert s3.stack[6] == 0x259;
      var s4 := Lt(s3);
      assert s4.stack[5] == 0x259;
      var s5 := IsZero(s4);
      assert s5.stack[5] == 0x259;
      var s6 := PushN(s5, 2, 0x12f0);
      assert s6.stack[0] == 0x12f0;
      assert s6.stack[6] == 0x259;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s7, gas - 1)
      else
        ExecuteFromCFGNode_s11(s7, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 185
    * Starting at 0x10db
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[5] == 0x259;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[6] == 0x259;
      var s3 := And(s2);
      assert s3.stack[5] == 0x259;
      var s4 := PushN(s3, 1, 0x01);
      assert s4.stack[6] == 0x259;
      var s5 := Eq(s4);
      assert s5.stack[5] == 0x259;
      var s6 := IsZero(s5);
      assert s6.stack[5] == 0x259;
      var s7 := PushN(s6, 2, 0x11e6);
      assert s7.stack[0] == 0x11e6;
      assert s7.stack[6] == 0x259;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s8, gas - 1)
      else
        ExecuteFromCFGNode_s12(s8, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 186
    * Starting at 0x10e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x02);
      assert s1.stack[5] == 0x259;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[6] == 0x259;
      var s3 := Dup(s2, 3);
      assert s3.stack[7] == 0x259;
      var s4 := PushN(s3, 1, 0x20);
      assert s4.stack[8] == 0x259;
      var s5 := Dup(s4, 2);
      assert s5.stack[9] == 0x259;
      var s6 := Lt(s5);
      assert s6.stack[8] == 0x259;
      var s7 := PushN(s6, 2, 0x10f5);
      assert s7.stack[0] == 0x10f5;
      assert s7.stack[9] == 0x259;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s8, gas - 1)
      else
        ExecuteFromCFGNode_s13(s8, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 187
    * Starting at 0x10f4
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 14
    * Segment Id for this node is: 188
    * Starting at 0x10f5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x259;
      var s2 := Add(s1);
      assert s2.stack[6] == 0x259;
      var s3 := SLoad(s2);
      assert s3.stack[6] == 0x259;
      var s4 := Dup(s3, 5);
      assert s4.stack[7] == 0x259;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[8] == 0x259;
      var s6 := MLoad(s5);
      assert s6.stack[8] == 0x259;
      var s7 := PushN(s6, 1, 0x20);
      assert s7.stack[9] == 0x259;
      var s8 := Add(s7);
      assert s8.stack[8] == 0x259;
      var s9 := Dup(s8, 1);
      assert s9.stack[9] == 0x259;
      var s10 := Dup(s9, 4);
      assert s10.stack[10] == 0x259;
      var s11 := Dup(s10, 2);
      assert s11.stack[11] == 0x259;
      var s12 := MStore(s11);
      assert s12.stack[9] == 0x259;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[10] == 0x259;
      var s14 := Add(s13);
      assert s14.stack[9] == 0x259;
      var s15 := Dup(s14, 3);
      assert s15.stack[10] == 0x259;
      var s16 := Dup(s15, 2);
      assert s16.stack[11] == 0x259;
      var s17 := MStore(s16);
      assert s17.stack[9] == 0x259;
      var s18 := PushN(s17, 1, 0x20);
      assert s18.stack[10] == 0x259;
      var s19 := Add(s18);
      assert s19.stack[9] == 0x259;
      var s20 := Swap(s19, 3);
      assert s20.stack[9] == 0x259;
      var s21 := Pop(s20);
      assert s21.stack[8] == 0x259;
      var s22 := Pop(s21);
      assert s22.stack[7] == 0x259;
      var s23 := Pop(s22);
      assert s23.stack[6] == 0x259;
      var s24 := PushN(s23, 1, 0x40);
      assert s24.stack[7] == 0x259;
      var s25 := MLoad(s24);
      assert s25.stack[7] == 0x259;
      var s26 := PushN(s25, 1, 0x20);
      assert s26.stack[8] == 0x259;
      var s27 := Dup(s26, 2);
      assert s27.stack[9] == 0x259;
      var s28 := Dup(s27, 4);
      assert s28.stack[10] == 0x259;
      var s29 := Sub(s28);
      assert s29.stack[9] == 0x259;
      var s30 := Sub(s29);
      assert s30.stack[8] == 0x259;
      var s31 := Dup(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s15(s31, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 189
    * Starting at 0x111a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.stack[7] == 0x259;
      var s2 := Swap(s1, 1);
      assert s2.stack[7] == 0x259;
      var s3 := PushN(s2, 1, 0x40);
      assert s3.stack[8] == 0x259;
      var s4 := MStore(s3);
      assert s4.stack[6] == 0x259;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[7] == 0x259;
      var s6 := MLoad(s5);
      assert s6.stack[7] == 0x259;
      var s7 := Dup(s6, 1);
      assert s7.stack[8] == 0x259;
      var s8 := Dup(s7, 3);
      assert s8.stack[9] == 0x259;
      var s9 := Dup(s8, 1);
      assert s9.stack[10] == 0x259;
      var s10 := MLoad(s9);
      assert s10.stack[10] == 0x259;
      var s11 := Swap(s10, 1);
      assert s11.stack[10] == 0x259;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[11] == 0x259;
      var s13 := Add(s12);
      assert s13.stack[10] == 0x259;
      var s14 := Swap(s13, 1);
      assert s14.stack[10] == 0x259;
      var s15 := Dup(s14, 1);
      assert s15.stack[11] == 0x259;
      var s16 := Dup(s15, 4);
      assert s16.stack[12] == 0x259;
      var s17 := Dup(s16, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s16(s17, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 190
    * Starting at 0x112e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[13] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[14] == 0x259;
      var s3 := Dup(s2, 4);
      assert s3.stack[15] == 0x259;
      var s4 := Lt(s3);
      assert s4.stack[14] == 0x259;
      var s5 := PushN(s4, 2, 0x116b);
      assert s5.stack[0] == 0x116b;
      assert s5.stack[15] == 0x259;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s18(s6, gas - 1)
      else
        ExecuteFromCFGNode_s17(s6, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 191
    * Starting at 0x1137
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1137 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[14] == 0x259;
      var s2 := MLoad(s1);
      assert s2.stack[14] == 0x259;
      var s3 := Dup(s2, 3);
      assert s3.stack[15] == 0x259;
      var s4 := MStore(s3);
      assert s4.stack[13] == 0x259;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[14] == 0x259;
      var s6 := Swap(s5, 1);
      assert s6.stack[14] == 0x259;
      var s7 := Swap(s6, 3);
      assert s7.stack[14] == 0x259;
      var s8 := Add(s7);
      assert s8.stack[13] == 0x259;
      var s9 := Swap(s8, 2);
      assert s9.stack[13] == 0x259;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[14] == 0x259;
      var s11 := Swap(s10, 2);
      assert s11.stack[14] == 0x259;
      var s12 := Dup(s11, 3);
      assert s12.stack[15] == 0x259;
      var s13 := Add(s12);
      assert s13.stack[14] == 0x259;
      var s14 := Swap(s13, 2);
      assert s14.stack[14] == 0x259;
      var s15 := Add(s14);
      assert s15.stack[13] == 0x259;
      var s16 := PushN(s15, 2, 0x112e);
      assert s16.stack[0] == 0x112e;
      assert s16.stack[14] == 0x259;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s17, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 192
    * Starting at 0x116b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[13] == 0x259;
      var s2 := MLoad(s1);
      assert s2.stack[13] == 0x259;
      var s3 := Dup(s2, 2);
      assert s3.stack[14] == 0x259;
      var s4 := MLoad(s3);
      assert s4.stack[14] == 0x259;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[15] == 0x259;
      var s6 := Swap(s5, 4);
      assert s6.stack[15] == 0x259;
      var s7 := Dup(s6, 5);
      assert s7.stack[16] == 0x259;
      var s8 := Sub(s7);
      assert s8.stack[15] == 0x259;
      var s9 := PushN(s8, 2, 0x0100);
      assert s9.stack[16] == 0x259;
      var s10 := Exp(s9);
      assert s10.stack[15] == 0x259;
      var s11 := PushN(s10, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s11.stack[16] == 0x259;
      var s12 := Add(s11);
      assert s12.stack[15] == 0x259;
      var s13 := Dup(s12, 1);
      assert s13.stack[16] == 0x259;
      var s14 := Not(s13);
      assert s14.stack[16] == 0x259;
      var s15 := Swap(s14, 1);
      assert s15.stack[16] == 0x259;
      var s16 := Swap(s15, 3);
      assert s16.stack[16] == 0x259;
      var s17 := And(s16);
      assert s17.stack[15] == 0x259;
      var s18 := Swap(s17, 2);
      assert s18.stack[15] == 0x259;
      var s19 := And(s18);
      assert s19.stack[14] == 0x259;
      var s20 := Or(s19);
      assert s20.stack[13] == 0x259;
      var s21 := Swap(s20, 1);
      assert s21.stack[13] == 0x259;
      var s22 := MStore(s21);
      assert s22.stack[11] == 0x259;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[12] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[12] == 0x259;
      var s25 := Swap(s24, 2);
      assert s25.stack[12] == 0x259;
      var s26 := Swap(s25, 1);
      assert s26.stack[12] == 0x259;
      var s27 := Swap(s26, 4);
      assert s27.stack[12] == 0x259;
      var s28 := Add(s27);
      assert s28.stack[11] == 0x259;
      var s29 := Swap(s28, 5);
      assert s29.stack[11] == 0x259;
      var s30 := Pop(s29);
      assert s30.stack[10] == 0x259;
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s19(s31, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 193
    * Starting at 0x11ae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[10] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[9] == 0x259;
      var s3 := Pop(s2);
      assert s3.stack[8] == 0x259;
      var s4 := Dup(s3, 1);
      assert s4.stack[9] == 0x259;
      var s5 := Dup(s4, 4);
      assert s5.stack[10] == 0x259;
      var s6 := Sub(s5);
      assert s6.stack[9] == 0x259;
      var s7 := Dup(s6, 2);
      assert s7.stack[10] == 0x259;
      var s8 := Dup(s7, 6);
      assert s8.stack[11] == 0x259;
      var s9 := Gas(s8);
      assert s9.stack[12] == 0x259;
      var s10 := StaticCall(s9);
      assert s10.stack[7] == 0x259;
      var s11 := IsZero(s10);
      assert s11.stack[7] == 0x259;
      var s12 := Dup(s11, 1);
      assert s12.stack[8] == 0x259;
      var s13 := IsZero(s12);
      assert s13.stack[8] == 0x259;
      var s14 := PushN(s13, 2, 0x11c8);
      assert s14.stack[0] == 0x11c8;
      assert s14.stack[9] == 0x259;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s15, gas - 1)
      else
        ExecuteFromCFGNode_s20(s15, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 194
    * Starting at 0x11bf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.stack[8] == 0x259;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[9] == 0x259;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x259;
      var s4 := ReturnDataCopy(s3);
      assert s4.stack[7] == 0x259;
      var s5 := ReturnDataSize(s4);
      assert s5.stack[8] == 0x259;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[9] == 0x259;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 21
    * Segment Id for this node is: 195
    * Starting at 0x11c8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[6] == 0x259;
      var s3 := Pop(s2);
      assert s3.stack[5] == 0x259;
      var s4 := Pop(s3);
      assert s4.stack[4] == 0x259;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[5] == 0x259;
      var s6 := MLoad(s5);
      assert s6.stack[5] == 0x259;
      var s7 := ReturnDataSize(s6);
      assert s7.stack[6] == 0x259;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[7] == 0x259;
      var s9 := Dup(s8, 2);
      assert s9.stack[8] == 0x259;
      var s10 := Lt(s9);
      assert s10.stack[7] == 0x259;
      var s11 := IsZero(s10);
      assert s11.stack[7] == 0x259;
      var s12 := PushN(s11, 2, 0x11dd);
      assert s12.stack[0] == 0x11dd;
      assert s12.stack[8] == 0x259;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s13, gas - 1)
      else
        ExecuteFromCFGNode_s22(s13, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 196
    * Starting at 0x11d9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[7] == 0x259;
      var s2 := Dup(s1, 1);
      assert s2.stack[8] == 0x259;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 23
    * Segment Id for this node is: 197
    * Starting at 0x11dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[5] == 0x259;
      var s3 := MLoad(s2);
      assert s3.stack[5] == 0x259;
      var s4 := Swap(s3, 3);
      assert s4.stack[5] == 0x259;
      var s5 := Pop(s4);
      assert s5.stack[4] == 0x259;
      var s6 := PushN(s5, 2, 0x12e2);
      assert s6.stack[0] == 0x12e2;
      assert s6.stack[5] == 0x259;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s7, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 210
    * Starting at 0x12e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x259;
      var s2 := PushN(s1, 1, 0x02);
      assert s2.stack[5] == 0x259;
      var s3 := Dup(s2, 3);
      assert s3.stack[6] == 0x259;
      var s4 := Div(s3);
      assert s4.stack[5] == 0x259;
      var s5 := Swap(s4, 2);
      assert s5.stack[5] == 0x259;
      var s6 := Pop(s5);
      assert s6.stack[4] == 0x259;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[5] == 0x259;
      var s8 := Add(s7);
      assert s8.stack[4] == 0x259;
      var s9 := PushN(s8, 2, 0x10d1);
      assert s9.stack[0] == 0x10d1;
      assert s9.stack[5] == 0x259;
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s10, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 198
    * Starting at 0x11e6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x259;
      var s2 := PushN(s1, 1, 0x02);
      assert s2.stack[5] == 0x259;
      var s3 := Dup(s2, 4);
      assert s3.stack[6] == 0x259;
      var s4 := PushN(s3, 1, 0x21);
      assert s4.stack[7] == 0x259;
      var s5 := Dup(s4, 4);
      assert s5.stack[8] == 0x259;
      var s6 := PushN(s5, 1, 0x20);
      assert s6.stack[9] == 0x259;
      var s7 := Dup(s6, 2);
      assert s7.stack[10] == 0x259;
      var s8 := Lt(s7);
      assert s8.stack[9] == 0x259;
      var s9 := PushN(s8, 2, 0x11f6);
      assert s9.stack[0] == 0x11f6;
      assert s9.stack[10] == 0x259;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s10, gas - 1)
      else
        ExecuteFromCFGNode_s26(s10, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 199
    * Starting at 0x11f5
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 27
    * Segment Id for this node is: 200
    * Starting at 0x11f6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0x259;
      var s2 := Add(s1);
      assert s2.stack[7] == 0x259;
      var s3 := SLoad(s2);
      assert s3.stack[7] == 0x259;
      var s4 := PushN(s3, 1, 0x40);
      assert s4.stack[8] == 0x259;
      var s5 := MLoad(s4);
      assert s5.stack[8] == 0x259;
      var s6 := PushN(s5, 1, 0x20);
      assert s6.stack[9] == 0x259;
      var s7 := Add(s6);
      assert s7.stack[8] == 0x259;
      var s8 := Dup(s7, 1);
      assert s8.stack[9] == 0x259;
      var s9 := Dup(s8, 4);
      assert s9.stack[10] == 0x259;
      var s10 := Dup(s9, 2);
      assert s10.stack[11] == 0x259;
      var s11 := MStore(s10);
      assert s11.stack[9] == 0x259;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[10] == 0x259;
      var s13 := Add(s12);
      assert s13.stack[9] == 0x259;
      var s14 := Dup(s13, 3);
      assert s14.stack[10] == 0x259;
      var s15 := Dup(s14, 2);
      assert s15.stack[11] == 0x259;
      var s16 := MStore(s15);
      assert s16.stack[9] == 0x259;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[10] == 0x259;
      var s18 := Add(s17);
      assert s18.stack[9] == 0x259;
      var s19 := Swap(s18, 3);
      assert s19.stack[9] == 0x259;
      var s20 := Pop(s19);
      assert s20.stack[8] == 0x259;
      var s21 := Pop(s20);
      assert s21.stack[7] == 0x259;
      var s22 := Pop(s21);
      assert s22.stack[6] == 0x259;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[7] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x259;
      var s25 := PushN(s24, 1, 0x20);
      assert s25.stack[8] == 0x259;
      var s26 := Dup(s25, 2);
      assert s26.stack[9] == 0x259;
      var s27 := Dup(s26, 4);
      assert s27.stack[10] == 0x259;
      var s28 := Sub(s27);
      assert s28.stack[9] == 0x259;
      var s29 := Sub(s28);
      assert s29.stack[8] == 0x259;
      var s30 := Dup(s29, 2);
      assert s30.stack[9] == 0x259;
      var s31 := MStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s28(s31, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 201
    * Starting at 0x121b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[7] == 0x259;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[8] == 0x259;
      var s3 := MStore(s2);
      assert s3.stack[6] == 0x259;
      var s4 := PushN(s3, 1, 0x40);
      assert s4.stack[7] == 0x259;
      var s5 := MLoad(s4);
      assert s5.stack[7] == 0x259;
      var s6 := Dup(s5, 1);
      assert s6.stack[8] == 0x259;
      var s7 := Dup(s6, 3);
      assert s7.stack[9] == 0x259;
      var s8 := Dup(s7, 1);
      assert s8.stack[10] == 0x259;
      var s9 := MLoad(s8);
      assert s9.stack[10] == 0x259;
      var s10 := Swap(s9, 1);
      assert s10.stack[10] == 0x259;
      var s11 := PushN(s10, 1, 0x20);
      assert s11.stack[11] == 0x259;
      var s12 := Add(s11);
      assert s12.stack[10] == 0x259;
      var s13 := Swap(s12, 1);
      assert s13.stack[10] == 0x259;
      var s14 := Dup(s13, 1);
      assert s14.stack[11] == 0x259;
      var s15 := Dup(s14, 4);
      assert s15.stack[12] == 0x259;
      var s16 := Dup(s15, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s29(s16, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 202
    * Starting at 0x122e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[13] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[14] == 0x259;
      var s3 := Dup(s2, 4);
      assert s3.stack[15] == 0x259;
      var s4 := Lt(s3);
      assert s4.stack[14] == 0x259;
      var s5 := PushN(s4, 2, 0x126b);
      assert s5.stack[0] == 0x126b;
      assert s5.stack[15] == 0x259;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s6, gas - 1)
      else
        ExecuteFromCFGNode_s30(s6, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 203
    * Starting at 0x1237
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1237 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[14] == 0x259;
      var s2 := MLoad(s1);
      assert s2.stack[14] == 0x259;
      var s3 := Dup(s2, 3);
      assert s3.stack[15] == 0x259;
      var s4 := MStore(s3);
      assert s4.stack[13] == 0x259;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[14] == 0x259;
      var s6 := Swap(s5, 1);
      assert s6.stack[14] == 0x259;
      var s7 := Swap(s6, 3);
      assert s7.stack[14] == 0x259;
      var s8 := Add(s7);
      assert s8.stack[13] == 0x259;
      var s9 := Swap(s8, 2);
      assert s9.stack[13] == 0x259;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[14] == 0x259;
      var s11 := Swap(s10, 2);
      assert s11.stack[14] == 0x259;
      var s12 := Dup(s11, 3);
      assert s12.stack[15] == 0x259;
      var s13 := Add(s12);
      assert s13.stack[14] == 0x259;
      var s14 := Swap(s13, 2);
      assert s14.stack[14] == 0x259;
      var s15 := Add(s14);
      assert s15.stack[13] == 0x259;
      var s16 := PushN(s15, 2, 0x122e);
      assert s16.stack[0] == 0x122e;
      assert s16.stack[14] == 0x259;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s17, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 204
    * Starting at 0x126b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[13] == 0x259;
      var s2 := MLoad(s1);
      assert s2.stack[13] == 0x259;
      var s3 := Dup(s2, 2);
      assert s3.stack[14] == 0x259;
      var s4 := MLoad(s3);
      assert s4.stack[14] == 0x259;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[15] == 0x259;
      var s6 := Swap(s5, 4);
      assert s6.stack[15] == 0x259;
      var s7 := Dup(s6, 5);
      assert s7.stack[16] == 0x259;
      var s8 := Sub(s7);
      assert s8.stack[15] == 0x259;
      var s9 := PushN(s8, 2, 0x0100);
      assert s9.stack[16] == 0x259;
      var s10 := Exp(s9);
      assert s10.stack[15] == 0x259;
      var s11 := PushN(s10, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s11.stack[16] == 0x259;
      var s12 := Add(s11);
      assert s12.stack[15] == 0x259;
      var s13 := Dup(s12, 1);
      assert s13.stack[16] == 0x259;
      var s14 := Not(s13);
      assert s14.stack[16] == 0x259;
      var s15 := Swap(s14, 1);
      assert s15.stack[16] == 0x259;
      var s16 := Swap(s15, 3);
      assert s16.stack[16] == 0x259;
      var s17 := And(s16);
      assert s17.stack[15] == 0x259;
      var s18 := Swap(s17, 2);
      assert s18.stack[15] == 0x259;
      var s19 := And(s18);
      assert s19.stack[14] == 0x259;
      var s20 := Or(s19);
      assert s20.stack[13] == 0x259;
      var s21 := Swap(s20, 1);
      assert s21.stack[13] == 0x259;
      var s22 := MStore(s21);
      assert s22.stack[11] == 0x259;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[12] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[12] == 0x259;
      var s25 := Swap(s24, 2);
      assert s25.stack[12] == 0x259;
      var s26 := Swap(s25, 1);
      assert s26.stack[12] == 0x259;
      var s27 := Swap(s26, 4);
      assert s27.stack[12] == 0x259;
      var s28 := Add(s27);
      assert s28.stack[11] == 0x259;
      var s29 := Swap(s28, 5);
      assert s29.stack[11] == 0x259;
      var s30 := Pop(s29);
      assert s30.stack[10] == 0x259;
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s32(s31, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 205
    * Starting at 0x12ae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[10] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[9] == 0x259;
      var s3 := Pop(s2);
      assert s3.stack[8] == 0x259;
      var s4 := Dup(s3, 1);
      assert s4.stack[9] == 0x259;
      var s5 := Dup(s4, 4);
      assert s5.stack[10] == 0x259;
      var s6 := Sub(s5);
      assert s6.stack[9] == 0x259;
      var s7 := Dup(s6, 2);
      assert s7.stack[10] == 0x259;
      var s8 := Dup(s7, 6);
      assert s8.stack[11] == 0x259;
      var s9 := Gas(s8);
      assert s9.stack[12] == 0x259;
      var s10 := StaticCall(s9);
      assert s10.stack[7] == 0x259;
      var s11 := IsZero(s10);
      assert s11.stack[7] == 0x259;
      var s12 := Dup(s11, 1);
      assert s12.stack[8] == 0x259;
      var s13 := IsZero(s12);
      assert s13.stack[8] == 0x259;
      var s14 := PushN(s13, 2, 0x12c8);
      assert s14.stack[0] == 0x12c8;
      assert s14.stack[9] == 0x259;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s15, gas - 1)
      else
        ExecuteFromCFGNode_s33(s15, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 206
    * Starting at 0x12bf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.stack[8] == 0x259;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[9] == 0x259;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x259;
      var s4 := ReturnDataCopy(s3);
      assert s4.stack[7] == 0x259;
      var s5 := ReturnDataSize(s4);
      assert s5.stack[8] == 0x259;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[9] == 0x259;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 34
    * Segment Id for this node is: 207
    * Starting at 0x12c8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[6] == 0x259;
      var s3 := Pop(s2);
      assert s3.stack[5] == 0x259;
      var s4 := Pop(s3);
      assert s4.stack[4] == 0x259;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[5] == 0x259;
      var s6 := MLoad(s5);
      assert s6.stack[5] == 0x259;
      var s7 := ReturnDataSize(s6);
      assert s7.stack[6] == 0x259;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[7] == 0x259;
      var s9 := Dup(s8, 2);
      assert s9.stack[8] == 0x259;
      var s10 := Lt(s9);
      assert s10.stack[7] == 0x259;
      var s11 := IsZero(s10);
      assert s11.stack[7] == 0x259;
      var s12 := PushN(s11, 2, 0x12dd);
      assert s12.stack[0] == 0x12dd;
      assert s12.stack[8] == 0x259;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s13, gas - 1)
      else
        ExecuteFromCFGNode_s35(s13, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 208
    * Starting at 0x12d9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[7] == 0x259;
      var s2 := Dup(s1, 1);
      assert s2.stack[8] == 0x259;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 36
    * Segment Id for this node is: 209
    * Starting at 0x12dd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[5] == 0x259;
      var s3 := MLoad(s2);
      assert s3.stack[5] == 0x259;
      var s4 := Swap(s3, 3);
      assert s4.stack[5] == 0x259;
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s24(s5, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 211
    * Starting at 0x12f0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[3] == 0x259;
      var s3 := PushN(s2, 1, 0x02);
      assert s3.stack[4] == 0x259;
      var s4 := Dup(s3, 3);
      assert s4.stack[5] == 0x259;
      var s5 := PushN(s4, 2, 0x12ff);
      assert s5.stack[0] == 0x12ff;
      assert s5.stack[6] == 0x259;
      var s6 := PushN(s5, 1, 0x20);
      assert s6.stack[1] == 0x12ff;
      assert s6.stack[7] == 0x259;
      var s7 := SLoad(s6);
      assert s7.stack[1] == 0x12ff;
      assert s7.stack[7] == 0x259;
      var s8 := PushN(s7, 2, 0x14ba);
      assert s8.stack[0] == 0x14ba;
      assert s8.stack[2] == 0x12ff;
      assert s8.stack[8] == 0x259;
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s9, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 226
    * Starting at 0x14ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x12ff

    requires s0.stack[7] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x12ff;
      assert s1.stack[7] == 0x259;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0x12ff;
      assert s2.stack[8] == 0x259;
      var s3 := Dup(s2, 1);
      assert s3.stack[3] == 0x12ff;
      assert s3.stack[9] == 0x259;
      var s4 := MLoad(s3);
      assert s4.stack[3] == 0x12ff;
      assert s4.stack[9] == 0x259;
      var s5 := PushN(s4, 1, 0x08);
      assert s5.stack[4] == 0x12ff;
      assert s5.stack[10] == 0x259;
      var s6 := Dup(s5, 1);
      assert s6.stack[5] == 0x12ff;
      assert s6.stack[11] == 0x259;
      var s7 := Dup(s6, 3);
      assert s7.stack[6] == 0x12ff;
      assert s7.stack[12] == 0x259;
      var s8 := MStore(s7);
      assert s8.stack[4] == 0x12ff;
      assert s8.stack[10] == 0x259;
      var s9 := Dup(s8, 2);
      assert s9.stack[5] == 0x12ff;
      assert s9.stack[11] == 0x259;
      var s10 := Dup(s9, 4);
      assert s10.stack[6] == 0x12ff;
      assert s10.stack[12] == 0x259;
      var s11 := Add(s10);
      assert s11.stack[5] == 0x12ff;
      assert s11.stack[11] == 0x259;
      var s12 := Swap(s11, 1);
      assert s12.stack[5] == 0x12ff;
      assert s12.stack[11] == 0x259;
      var s13 := Swap(s12, 3);
      assert s13.stack[5] == 0x12ff;
      assert s13.stack[11] == 0x259;
      var s14 := MStore(s13);
      assert s14.stack[3] == 0x12ff;
      assert s14.stack[9] == 0x259;
      var s15 := PushN(s14, 1, 0x60);
      assert s15.stack[4] == 0x12ff;
      assert s15.stack[10] == 0x259;
      var s16 := Swap(s15, 2);
      assert s16.stack[4] == 0x12ff;
      assert s16.stack[10] == 0x259;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[5] == 0x12ff;
      assert s17.stack[11] == 0x259;
      var s18 := Dup(s17, 3);
      assert s18.stack[6] == 0x12ff;
      assert s18.stack[12] == 0x259;
      var s19 := Add(s18);
      assert s19.stack[5] == 0x12ff;
      assert s19.stack[11] == 0x259;
      var s20 := Dup(s19, 2);
      assert s20.stack[6] == 0x12ff;
      assert s20.stack[12] == 0x259;
      var s21 := Dup(s20, 1);
      assert s21.stack[7] == 0x12ff;
      assert s21.stack[13] == 0x259;
      var s22 := CallDataSize(s21);
      assert s22.stack[8] == 0x12ff;
      assert s22.stack[14] == 0x259;
      var s23 := Dup(s22, 4);
      assert s23.stack[9] == 0x12ff;
      assert s23.stack[15] == 0x259;
      var s24 := CallDataCopy(s23);
      assert s24.stack[6] == 0x12ff;
      assert s24.stack[12] == 0x259;
      var s25 := Add(s24);
      assert s25.stack[5] == 0x12ff;
      assert s25.stack[11] == 0x259;
      var s26 := Swap(s25, 1);
      assert s26.stack[5] == 0x12ff;
      assert s26.stack[11] == 0x259;
      var s27 := Pop(s26);
      assert s27.stack[4] == 0x12ff;
      assert s27.stack[10] == 0x259;
      var s28 := Pop(s27);
      assert s28.stack[3] == 0x12ff;
      assert s28.stack[9] == 0x259;
      var s29 := Swap(s28, 1);
      assert s29.stack[3] == 0x12ff;
      assert s29.stack[9] == 0x259;
      var s30 := Pop(s29);
      assert s30.stack[2] == 0x12ff;
      assert s30.stack[8] == 0x259;
      var s31 := PushN(s30, 1, 0xc0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s39(s31, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 227
    * Starting at 0x14de
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x12ff

    requires s0.stack[9] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[4] == 0x12ff;
      assert s1.stack[10] == 0x259;
      var s2 := Swap(s1, 1);
      assert s2.stack[4] == 0x12ff;
      assert s2.stack[10] == 0x259;
      var s3 := Shl(s2);
      assert s3.stack[3] == 0x12ff;
      assert s3.stack[9] == 0x259;
      var s4 := Dup(s3, 1);
      assert s4.stack[4] == 0x12ff;
      assert s4.stack[10] == 0x259;
      var s5 := PushN(s4, 1, 0x07);
      assert s5.stack[5] == 0x12ff;
      assert s5.stack[11] == 0x259;
      var s6 := Byte(s5);
      assert s6.stack[4] == 0x12ff;
      assert s6.stack[10] == 0x259;
      var s7 := PushN(s6, 1, 0xf8);
      assert s7.stack[5] == 0x12ff;
      assert s7.stack[11] == 0x259;
      var s8 := Shl(s7);
      assert s8.stack[4] == 0x12ff;
      assert s8.stack[10] == 0x259;
      var s9 := Dup(s8, 3);
      assert s9.stack[5] == 0x12ff;
      assert s9.stack[11] == 0x259;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[6] == 0x12ff;
      assert s10.stack[12] == 0x259;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x12ff;
      assert s11.stack[13] == 0x259;
      var s12 := MLoad(s11);
      assert s12.stack[7] == 0x12ff;
      assert s12.stack[13] == 0x259;
      var s13 := Dup(s12, 2);
      assert s13.stack[8] == 0x12ff;
      assert s13.stack[14] == 0x259;
      var s14 := Lt(s13);
      assert s14.stack[7] == 0x12ff;
      assert s14.stack[13] == 0x259;
      var s15 := PushN(s14, 2, 0x14f4);
      assert s15.stack[0] == 0x14f4;
      assert s15.stack[8] == 0x12ff;
      assert s15.stack[14] == 0x259;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s16, gas - 1)
      else
        ExecuteFromCFGNode_s40(s16, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 228
    * Starting at 0x14f3
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 41
    * Segment Id for this node is: 229
    * Starting at 0x14f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x12ff;
      assert s1.stack[12] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x12ff;
      assert s2.stack[13] == 0x259;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x12ff;
      assert s3.stack[12] == 0x259;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x12ff;
      assert s4.stack[11] == 0x259;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x12ff;
      assert s5.stack[11] == 0x259;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x12ff;
      assert s6.stack[12] == 0x259;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x12ff;
      assert s7.stack[12] == 0x259;
      var s8 := And(s7);
      assert s8.stack[5] == 0x12ff;
      assert s8.stack[11] == 0x259;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x12ff;
      assert s9.stack[11] == 0x259;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x12ff;
      assert s10.stack[12] == 0x259;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x12ff;
      assert s11.stack[13] == 0x259;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x12ff;
      assert s12.stack[12] == 0x259;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x12ff;
      assert s13.stack[12] == 0x259;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x12ff;
      assert s14.stack[10] == 0x259;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x12ff;
      assert s15.stack[9] == 0x259;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x12ff;
      assert s16.stack[10] == 0x259;
      var s17 := PushN(s16, 1, 0x06);
      assert s17.stack[5] == 0x12ff;
      assert s17.stack[11] == 0x259;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x12ff;
      assert s18.stack[10] == 0x259;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x12ff;
      assert s19.stack[11] == 0x259;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x12ff;
      assert s20.stack[10] == 0x259;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x12ff;
      assert s21.stack[11] == 0x259;
      var s22 := PushN(s21, 1, 0x01);
      assert s22.stack[6] == 0x12ff;
      assert s22.stack[12] == 0x259;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x12ff;
      assert s23.stack[13] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x12ff;
      assert s24.stack[13] == 0x259;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x12ff;
      assert s25.stack[14] == 0x259;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x12ff;
      assert s26.stack[13] == 0x259;
      var s27 := PushN(s26, 2, 0x1537);
      assert s27.stack[0] == 0x1537;
      assert s27.stack[8] == 0x12ff;
      assert s27.stack[14] == 0x259;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s28, gas - 1)
      else
        ExecuteFromCFGNode_s42(s28, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 230
    * Starting at 0x1536
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 43
    * Segment Id for this node is: 231
    * Starting at 0x1537
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1537 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x12ff;
      assert s1.stack[12] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x12ff;
      assert s2.stack[13] == 0x259;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x12ff;
      assert s3.stack[12] == 0x259;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x12ff;
      assert s4.stack[11] == 0x259;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x12ff;
      assert s5.stack[11] == 0x259;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x12ff;
      assert s6.stack[12] == 0x259;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x12ff;
      assert s7.stack[12] == 0x259;
      var s8 := And(s7);
      assert s8.stack[5] == 0x12ff;
      assert s8.stack[11] == 0x259;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x12ff;
      assert s9.stack[11] == 0x259;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x12ff;
      assert s10.stack[12] == 0x259;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x12ff;
      assert s11.stack[13] == 0x259;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x12ff;
      assert s12.stack[12] == 0x259;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x12ff;
      assert s13.stack[12] == 0x259;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x12ff;
      assert s14.stack[10] == 0x259;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x12ff;
      assert s15.stack[9] == 0x259;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x12ff;
      assert s16.stack[10] == 0x259;
      var s17 := PushN(s16, 1, 0x05);
      assert s17.stack[5] == 0x12ff;
      assert s17.stack[11] == 0x259;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x12ff;
      assert s18.stack[10] == 0x259;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x12ff;
      assert s19.stack[11] == 0x259;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x12ff;
      assert s20.stack[10] == 0x259;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x12ff;
      assert s21.stack[11] == 0x259;
      var s22 := PushN(s21, 1, 0x02);
      assert s22.stack[6] == 0x12ff;
      assert s22.stack[12] == 0x259;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x12ff;
      assert s23.stack[13] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x12ff;
      assert s24.stack[13] == 0x259;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x12ff;
      assert s25.stack[14] == 0x259;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x12ff;
      assert s26.stack[13] == 0x259;
      var s27 := PushN(s26, 2, 0x157a);
      assert s27.stack[0] == 0x157a;
      assert s27.stack[8] == 0x12ff;
      assert s27.stack[14] == 0x259;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s28, gas - 1)
      else
        ExecuteFromCFGNode_s44(s28, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 232
    * Starting at 0x1579
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1579 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 45
    * Segment Id for this node is: 233
    * Starting at 0x157a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x12ff;
      assert s1.stack[12] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x12ff;
      assert s2.stack[13] == 0x259;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x12ff;
      assert s3.stack[12] == 0x259;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x12ff;
      assert s4.stack[11] == 0x259;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x12ff;
      assert s5.stack[11] == 0x259;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x12ff;
      assert s6.stack[12] == 0x259;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x12ff;
      assert s7.stack[12] == 0x259;
      var s8 := And(s7);
      assert s8.stack[5] == 0x12ff;
      assert s8.stack[11] == 0x259;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x12ff;
      assert s9.stack[11] == 0x259;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x12ff;
      assert s10.stack[12] == 0x259;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x12ff;
      assert s11.stack[13] == 0x259;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x12ff;
      assert s12.stack[12] == 0x259;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x12ff;
      assert s13.stack[12] == 0x259;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x12ff;
      assert s14.stack[10] == 0x259;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x12ff;
      assert s15.stack[9] == 0x259;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x12ff;
      assert s16.stack[10] == 0x259;
      var s17 := PushN(s16, 1, 0x04);
      assert s17.stack[5] == 0x12ff;
      assert s17.stack[11] == 0x259;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x12ff;
      assert s18.stack[10] == 0x259;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x12ff;
      assert s19.stack[11] == 0x259;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x12ff;
      assert s20.stack[10] == 0x259;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x12ff;
      assert s21.stack[11] == 0x259;
      var s22 := PushN(s21, 1, 0x03);
      assert s22.stack[6] == 0x12ff;
      assert s22.stack[12] == 0x259;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x12ff;
      assert s23.stack[13] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x12ff;
      assert s24.stack[13] == 0x259;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x12ff;
      assert s25.stack[14] == 0x259;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x12ff;
      assert s26.stack[13] == 0x259;
      var s27 := PushN(s26, 2, 0x15bd);
      assert s27.stack[0] == 0x15bd;
      assert s27.stack[8] == 0x12ff;
      assert s27.stack[14] == 0x259;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s28, gas - 1)
      else
        ExecuteFromCFGNode_s46(s28, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 234
    * Starting at 0x15bc
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 47
    * Segment Id for this node is: 235
    * Starting at 0x15bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x12ff;
      assert s1.stack[12] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x12ff;
      assert s2.stack[13] == 0x259;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x12ff;
      assert s3.stack[12] == 0x259;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x12ff;
      assert s4.stack[11] == 0x259;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x12ff;
      assert s5.stack[11] == 0x259;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x12ff;
      assert s6.stack[12] == 0x259;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x12ff;
      assert s7.stack[12] == 0x259;
      var s8 := And(s7);
      assert s8.stack[5] == 0x12ff;
      assert s8.stack[11] == 0x259;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x12ff;
      assert s9.stack[11] == 0x259;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x12ff;
      assert s10.stack[12] == 0x259;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x12ff;
      assert s11.stack[13] == 0x259;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x12ff;
      assert s12.stack[12] == 0x259;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x12ff;
      assert s13.stack[12] == 0x259;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x12ff;
      assert s14.stack[10] == 0x259;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x12ff;
      assert s15.stack[9] == 0x259;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x12ff;
      assert s16.stack[10] == 0x259;
      var s17 := PushN(s16, 1, 0x03);
      assert s17.stack[5] == 0x12ff;
      assert s17.stack[11] == 0x259;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x12ff;
      assert s18.stack[10] == 0x259;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x12ff;
      assert s19.stack[11] == 0x259;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x12ff;
      assert s20.stack[10] == 0x259;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x12ff;
      assert s21.stack[11] == 0x259;
      var s22 := PushN(s21, 1, 0x04);
      assert s22.stack[6] == 0x12ff;
      assert s22.stack[12] == 0x259;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x12ff;
      assert s23.stack[13] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x12ff;
      assert s24.stack[13] == 0x259;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x12ff;
      assert s25.stack[14] == 0x259;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x12ff;
      assert s26.stack[13] == 0x259;
      var s27 := PushN(s26, 2, 0x1600);
      assert s27.stack[0] == 0x1600;
      assert s27.stack[8] == 0x12ff;
      assert s27.stack[14] == 0x259;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s28, gas - 1)
      else
        ExecuteFromCFGNode_s48(s28, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 236
    * Starting at 0x15ff
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 49
    * Segment Id for this node is: 237
    * Starting at 0x1600
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1600 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x12ff;
      assert s1.stack[12] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x12ff;
      assert s2.stack[13] == 0x259;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x12ff;
      assert s3.stack[12] == 0x259;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x12ff;
      assert s4.stack[11] == 0x259;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x12ff;
      assert s5.stack[11] == 0x259;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x12ff;
      assert s6.stack[12] == 0x259;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x12ff;
      assert s7.stack[12] == 0x259;
      var s8 := And(s7);
      assert s8.stack[5] == 0x12ff;
      assert s8.stack[11] == 0x259;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x12ff;
      assert s9.stack[11] == 0x259;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x12ff;
      assert s10.stack[12] == 0x259;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x12ff;
      assert s11.stack[13] == 0x259;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x12ff;
      assert s12.stack[12] == 0x259;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x12ff;
      assert s13.stack[12] == 0x259;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x12ff;
      assert s14.stack[10] == 0x259;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x12ff;
      assert s15.stack[9] == 0x259;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x12ff;
      assert s16.stack[10] == 0x259;
      var s17 := PushN(s16, 1, 0x02);
      assert s17.stack[5] == 0x12ff;
      assert s17.stack[11] == 0x259;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x12ff;
      assert s18.stack[10] == 0x259;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x12ff;
      assert s19.stack[11] == 0x259;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x12ff;
      assert s20.stack[10] == 0x259;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x12ff;
      assert s21.stack[11] == 0x259;
      var s22 := PushN(s21, 1, 0x05);
      assert s22.stack[6] == 0x12ff;
      assert s22.stack[12] == 0x259;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x12ff;
      assert s23.stack[13] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x12ff;
      assert s24.stack[13] == 0x259;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x12ff;
      assert s25.stack[14] == 0x259;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x12ff;
      assert s26.stack[13] == 0x259;
      var s27 := PushN(s26, 2, 0x1643);
      assert s27.stack[0] == 0x1643;
      assert s27.stack[8] == 0x12ff;
      assert s27.stack[14] == 0x259;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s28, gas - 1)
      else
        ExecuteFromCFGNode_s50(s28, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 238
    * Starting at 0x1642
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1642 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 51
    * Segment Id for this node is: 239
    * Starting at 0x1643
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1643 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x12ff;
      assert s1.stack[12] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x12ff;
      assert s2.stack[13] == 0x259;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x12ff;
      assert s3.stack[12] == 0x259;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x12ff;
      assert s4.stack[11] == 0x259;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x12ff;
      assert s5.stack[11] == 0x259;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x12ff;
      assert s6.stack[12] == 0x259;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x12ff;
      assert s7.stack[12] == 0x259;
      var s8 := And(s7);
      assert s8.stack[5] == 0x12ff;
      assert s8.stack[11] == 0x259;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x12ff;
      assert s9.stack[11] == 0x259;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x12ff;
      assert s10.stack[12] == 0x259;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x12ff;
      assert s11.stack[13] == 0x259;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x12ff;
      assert s12.stack[12] == 0x259;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x12ff;
      assert s13.stack[12] == 0x259;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x12ff;
      assert s14.stack[10] == 0x259;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x12ff;
      assert s15.stack[9] == 0x259;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x12ff;
      assert s16.stack[10] == 0x259;
      var s17 := PushN(s16, 1, 0x01);
      assert s17.stack[5] == 0x12ff;
      assert s17.stack[11] == 0x259;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x12ff;
      assert s18.stack[10] == 0x259;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x12ff;
      assert s19.stack[11] == 0x259;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x12ff;
      assert s20.stack[10] == 0x259;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x12ff;
      assert s21.stack[11] == 0x259;
      var s22 := PushN(s21, 1, 0x06);
      assert s22.stack[6] == 0x12ff;
      assert s22.stack[12] == 0x259;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x12ff;
      assert s23.stack[13] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x12ff;
      assert s24.stack[13] == 0x259;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x12ff;
      assert s25.stack[14] == 0x259;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x12ff;
      assert s26.stack[13] == 0x259;
      var s27 := PushN(s26, 2, 0x1686);
      assert s27.stack[0] == 0x1686;
      assert s27.stack[8] == 0x12ff;
      assert s27.stack[14] == 0x259;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s28, gas - 1)
      else
        ExecuteFromCFGNode_s52(s28, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 240
    * Starting at 0x1685
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1685 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 53
    * Segment Id for this node is: 241
    * Starting at 0x1686
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1686 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x12ff;
      assert s1.stack[12] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x12ff;
      assert s2.stack[13] == 0x259;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x12ff;
      assert s3.stack[12] == 0x259;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x12ff;
      assert s4.stack[11] == 0x259;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x12ff;
      assert s5.stack[11] == 0x259;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x12ff;
      assert s6.stack[12] == 0x259;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x12ff;
      assert s7.stack[12] == 0x259;
      var s8 := And(s7);
      assert s8.stack[5] == 0x12ff;
      assert s8.stack[11] == 0x259;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x12ff;
      assert s9.stack[11] == 0x259;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x12ff;
      assert s10.stack[12] == 0x259;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x12ff;
      assert s11.stack[13] == 0x259;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x12ff;
      assert s12.stack[12] == 0x259;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x12ff;
      assert s13.stack[12] == 0x259;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x12ff;
      assert s14.stack[10] == 0x259;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x12ff;
      assert s15.stack[9] == 0x259;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x12ff;
      assert s16.stack[10] == 0x259;
      var s17 := PushN(s16, 1, 0x00);
      assert s17.stack[5] == 0x12ff;
      assert s17.stack[11] == 0x259;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x12ff;
      assert s18.stack[10] == 0x259;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x12ff;
      assert s19.stack[11] == 0x259;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x12ff;
      assert s20.stack[10] == 0x259;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x12ff;
      assert s21.stack[11] == 0x259;
      var s22 := PushN(s21, 1, 0x07);
      assert s22.stack[6] == 0x12ff;
      assert s22.stack[12] == 0x259;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x12ff;
      assert s23.stack[13] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x12ff;
      assert s24.stack[13] == 0x259;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x12ff;
      assert s25.stack[14] == 0x259;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x12ff;
      assert s26.stack[13] == 0x259;
      var s27 := PushN(s26, 2, 0x16c9);
      assert s27.stack[0] == 0x16c9;
      assert s27.stack[8] == 0x12ff;
      assert s27.stack[14] == 0x259;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s28, gas - 1)
      else
        ExecuteFromCFGNode_s54(s28, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 242
    * Starting at 0x16c8
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 55
    * Segment Id for this node is: 243
    * Starting at 0x16c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x12ff

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x12ff;
      assert s1.stack[12] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x12ff;
      assert s2.stack[13] == 0x259;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x12ff;
      assert s3.stack[12] == 0x259;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x12ff;
      assert s4.stack[11] == 0x259;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x12ff;
      assert s5.stack[11] == 0x259;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x12ff;
      assert s6.stack[12] == 0x259;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x12ff;
      assert s7.stack[12] == 0x259;
      var s8 := And(s7);
      assert s8.stack[5] == 0x12ff;
      assert s8.stack[11] == 0x259;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x12ff;
      assert s9.stack[11] == 0x259;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x12ff;
      assert s10.stack[12] == 0x259;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x12ff;
      assert s11.stack[13] == 0x259;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x12ff;
      assert s12.stack[12] == 0x259;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x12ff;
      assert s13.stack[12] == 0x259;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x12ff;
      assert s14.stack[10] == 0x259;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x12ff;
      assert s15.stack[9] == 0x259;
      var s16 := Pop(s15);
      assert s16.stack[2] == 0x12ff;
      assert s16.stack[8] == 0x259;
      var s17 := Swap(s16, 2);
      assert s17.stack[0] == 0x12ff;
      assert s17.stack[8] == 0x259;
      var s18 := Swap(s17, 1);
      assert s18.stack[1] == 0x12ff;
      assert s18.stack[8] == 0x259;
      var s19 := Pop(s18);
      assert s19.stack[0] == 0x12ff;
      assert s19.stack[7] == 0x259;
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s20, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 212
    * Starting at 0x12ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x259;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[7] == 0x259;
      var s3 := PushN(s2, 1, 0x40);
      assert s3.stack[8] == 0x259;
      var s4 := Shl(s3);
      assert s4.stack[7] == 0x259;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[8] == 0x259;
      var s6 := MLoad(s5);
      assert s6.stack[8] == 0x259;
      var s7 := PushN(s6, 1, 0x20);
      assert s7.stack[9] == 0x259;
      var s8 := Add(s7);
      assert s8.stack[8] == 0x259;
      var s9 := Dup(s8, 1);
      assert s9.stack[9] == 0x259;
      var s10 := Dup(s9, 5);
      assert s10.stack[10] == 0x259;
      var s11 := Dup(s10, 2);
      assert s11.stack[11] == 0x259;
      var s12 := MStore(s11);
      assert s12.stack[9] == 0x259;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[10] == 0x259;
      var s14 := Add(s13);
      assert s14.stack[9] == 0x259;
      var s15 := Dup(s14, 4);
      assert s15.stack[10] == 0x259;
      var s16 := Dup(s15, 1);
      assert s16.stack[11] == 0x259;
      var s17 := MLoad(s16);
      assert s17.stack[11] == 0x259;
      var s18 := Swap(s17, 1);
      assert s18.stack[11] == 0x259;
      var s19 := PushN(s18, 1, 0x20);
      assert s19.stack[12] == 0x259;
      var s20 := Add(s19);
      assert s20.stack[11] == 0x259;
      var s21 := Swap(s20, 1);
      assert s21.stack[11] == 0x259;
      var s22 := Dup(s21, 1);
      assert s22.stack[12] == 0x259;
      var s23 := Dup(s22, 4);
      assert s23.stack[13] == 0x259;
      var s24 := Dup(s23, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s57(s24, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 213
    * Starting at 0x131d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[14] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[15] == 0x259;
      var s3 := Dup(s2, 4);
      assert s3.stack[16] == 0x259;
      var s4 := Lt(s3);
      assert s4.stack[15] == 0x259;
      var s5 := PushN(s4, 2, 0x135a);
      assert s5.stack[0] == 0x135a;
      assert s5.stack[16] == 0x259;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s6, gas - 1)
      else
        ExecuteFromCFGNode_s58(s6, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 214
    * Starting at 0x1326
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1326 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[15] == 0x259;
      var s2 := MLoad(s1);
      assert s2.stack[15] == 0x259;
      var s3 := Dup(s2, 3);
      assert s3.stack[16] == 0x259;
      var s4 := MStore(s3);
      assert s4.stack[14] == 0x259;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[15] == 0x259;
      var s6 := Swap(s5, 1);
      assert s6.stack[15] == 0x259;
      var s7 := Swap(s6, 3);
      assert s7.stack[15] == 0x259;
      var s8 := Add(s7);
      assert s8.stack[14] == 0x259;
      var s9 := Swap(s8, 2);
      assert s9.stack[14] == 0x259;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[15] == 0x259;
      var s11 := Swap(s10, 2);
      assert s11.stack[15] == 0x259;
      var s12 := Dup(s11, 3);
      assert s12.stack[16] == 0x259;
      var s13 := Add(s12);
      assert s13.stack[15] == 0x259;
      var s14 := Swap(s13, 2);
      assert s14.stack[15] == 0x259;
      var s15 := Add(s14);
      assert s15.stack[14] == 0x259;
      var s16 := PushN(s15, 2, 0x131d);
      assert s16.stack[0] == 0x131d;
      assert s16.stack[15] == 0x259;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s17, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 215
    * Starting at 0x135a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[14] == 0x259;
      var s2 := MLoad(s1);
      assert s2.stack[14] == 0x259;
      var s3 := Dup(s2, 2);
      assert s3.stack[15] == 0x259;
      var s4 := MLoad(s3);
      assert s4.stack[15] == 0x259;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[16] == 0x259;
      var s6 := Swap(s5, 4);
      assert s6.stack[16] == 0x259;
      var s7 := Dup(s6, 5);
      assert s7.stack[17] == 0x259;
      var s8 := Sub(s7);
      assert s8.stack[16] == 0x259;
      var s9 := PushN(s8, 2, 0x0100);
      assert s9.stack[17] == 0x259;
      var s10 := Exp(s9);
      assert s10.stack[16] == 0x259;
      var s11 := PushN(s10, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s11.stack[17] == 0x259;
      var s12 := Add(s11);
      assert s12.stack[16] == 0x259;
      var s13 := Dup(s12, 1);
      assert s13.stack[17] == 0x259;
      var s14 := Not(s13);
      assert s14.stack[17] == 0x259;
      var s15 := Swap(s14, 1);
      assert s15.stack[17] == 0x259;
      var s16 := Swap(s15, 3);
      assert s16.stack[17] == 0x259;
      var s17 := And(s16);
      assert s17.stack[16] == 0x259;
      var s18 := Swap(s17, 2);
      assert s18.stack[16] == 0x259;
      var s19 := And(s18);
      assert s19.stack[15] == 0x259;
      var s20 := Or(s19);
      assert s20.stack[14] == 0x259;
      var s21 := Swap(s20, 1);
      assert s21.stack[14] == 0x259;
      var s22 := MStore(s21);
      assert s22.stack[12] == 0x259;
      var s23 := PushN(s22, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000);
      assert s23.stack[13] == 0x259;
      var s24 := Swap(s23, 6);
      assert s24.stack[13] == 0x259;
      var s25 := Swap(s24, 1);
      assert s25.stack[13] == 0x259;
      var s26 := Swap(s25, 6);
      assert s26.stack[13] == 0x259;
      var s27 := And(s26);
      assert s27.stack[12] == 0x259;
      var s28 := Swap(s27, 3);
      assert s28.stack[12] == 0x259;
      var s29 := Add(s28);
      assert s29.stack[11] == 0x259;
      var s30 := Swap(s29, 2);
      assert s30.stack[11] == 0x259;
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s60(s31, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 216
    * Starting at 0x13bc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.stack[10] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[9] == 0x259;
      var s3 := PushN(s2, 1, 0x40);
      assert s3.stack[10] == 0x259;
      var s4 := Dup(s3, 1);
      assert s4.stack[11] == 0x259;
      var s5 := MLoad(s4);
      assert s5.stack[11] == 0x259;
      var s6 := Dup(s5, 1);
      assert s6.stack[12] == 0x259;
      var s7 := Dup(s6, 4);
      assert s7.stack[13] == 0x259;
      var s8 := Sub(s7);
      assert s8.stack[12] == 0x259;
      var s9 := PushN(s8, 32, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8);
      assert s9.stack[13] == 0x259;
      var s10 := Add(s9);
      assert s10.stack[12] == 0x259;
      var s11 := Dup(s10, 2);
      assert s11.stack[13] == 0x259;
      var s12 := MStore(s11);
      assert s12.stack[11] == 0x259;
      var s13 := PushN(s12, 1, 0x18);
      assert s13.stack[12] == 0x259;
      var s14 := Swap(s13, 1);
      assert s14.stack[12] == 0x259;
      var s15 := Swap(s14, 3);
      assert s15.stack[12] == 0x259;
      var s16 := Add(s15);
      assert s16.stack[11] == 0x259;
      var s17 := Swap(s16, 1);
      assert s17.stack[11] == 0x259;
      var s18 := Dup(s17, 2);
      assert s18.stack[12] == 0x259;
      var s19 := Swap(s18, 1);
      assert s19.stack[12] == 0x259;
      var s20 := MStore(s19);
      assert s20.stack[10] == 0x259;
      var s21 := Dup(s20, 2);
      assert s21.stack[11] == 0x259;
      var s22 := MLoad(s21);
      assert s22.stack[11] == 0x259;
      var s23 := Swap(s22, 2);
      assert s23.stack[11] == 0x259;
      var s24 := Swap(s23, 6);
      assert s24.stack[11] == 0x259;
      var s25 := Pop(s24);
      assert s25.stack[10] == 0x259;
      var s26 := Swap(s25, 4);
      assert s26.stack[10] == 0x259;
      var s27 := Pop(s26);
      assert s27.stack[9] == 0x259;
      var s28 := Dup(s27, 4);
      assert s28.stack[10] == 0x259;
      var s29 := Swap(s28, 3);
      assert s29.stack[10] == 0x259;
      var s30 := Dup(s29, 6);
      assert s30.stack[11] == 0x259;
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s61(s31, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 217
    * Starting at 0x13fd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 2);
      assert s1.stack[10] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[9] == 0x259;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x259;
      var s4 := Dup(s3, 4);
      assert s4.stack[11] == 0x259;
      var s5 := Dup(s4, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s62(s5, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 218
    * Starting at 0x1402
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1402 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[12] == 0x259;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[13] == 0x259;
      var s3 := Dup(s2, 4);
      assert s3.stack[14] == 0x259;
      var s4 := Lt(s3);
      assert s4.stack[13] == 0x259;
      var s5 := PushN(s4, 2, 0x143f);
      assert s5.stack[0] == 0x143f;
      assert s5.stack[14] == 0x259;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s6, gas - 1)
      else
        ExecuteFromCFGNode_s63(s6, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 219
    * Starting at 0x140b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[13] == 0x259;
      var s2 := MLoad(s1);
      assert s2.stack[13] == 0x259;
      var s3 := Dup(s2, 3);
      assert s3.stack[14] == 0x259;
      var s4 := MStore(s3);
      assert s4.stack[12] == 0x259;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[13] == 0x259;
      var s6 := Swap(s5, 1);
      assert s6.stack[13] == 0x259;
      var s7 := Swap(s6, 3);
      assert s7.stack[13] == 0x259;
      var s8 := Add(s7);
      assert s8.stack[12] == 0x259;
      var s9 := Swap(s8, 2);
      assert s9.stack[12] == 0x259;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[13] == 0x259;
      var s11 := Swap(s10, 2);
      assert s11.stack[13] == 0x259;
      var s12 := Dup(s11, 3);
      assert s12.stack[14] == 0x259;
      var s13 := Add(s12);
      assert s13.stack[13] == 0x259;
      var s14 := Swap(s13, 2);
      assert s14.stack[13] == 0x259;
      var s15 := Add(s14);
      assert s15.stack[12] == 0x259;
      var s16 := PushN(s15, 2, 0x1402);
      assert s16.stack[0] == 0x1402;
      assert s16.stack[13] == 0x259;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s17, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 220
    * Starting at 0x143f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[12] == 0x259;
      var s2 := MLoad(s1);
      assert s2.stack[12] == 0x259;
      var s3 := Dup(s2, 2);
      assert s3.stack[13] == 0x259;
      var s4 := MLoad(s3);
      assert s4.stack[13] == 0x259;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[14] == 0x259;
      var s6 := Swap(s5, 4);
      assert s6.stack[14] == 0x259;
      var s7 := Dup(s6, 5);
      assert s7.stack[15] == 0x259;
      var s8 := Sub(s7);
      assert s8.stack[14] == 0x259;
      var s9 := PushN(s8, 2, 0x0100);
      assert s9.stack[15] == 0x259;
      var s10 := Exp(s9);
      assert s10.stack[14] == 0x259;
      var s11 := PushN(s10, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s11.stack[15] == 0x259;
      var s12 := Add(s11);
      assert s12.stack[14] == 0x259;
      var s13 := Dup(s12, 1);
      assert s13.stack[15] == 0x259;
      var s14 := Not(s13);
      assert s14.stack[15] == 0x259;
      var s15 := Swap(s14, 1);
      assert s15.stack[15] == 0x259;
      var s16 := Swap(s15, 3);
      assert s16.stack[15] == 0x259;
      var s17 := And(s16);
      assert s17.stack[14] == 0x259;
      var s18 := Swap(s17, 2);
      assert s18.stack[14] == 0x259;
      var s19 := And(s18);
      assert s19.stack[13] == 0x259;
      var s20 := Or(s19);
      assert s20.stack[12] == 0x259;
      var s21 := Swap(s20, 1);
      assert s21.stack[12] == 0x259;
      var s22 := MStore(s21);
      assert s22.stack[10] == 0x259;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[11] == 0x259;
      var s24 := MLoad(s23);
      assert s24.stack[11] == 0x259;
      var s25 := Swap(s24, 2);
      assert s25.stack[11] == 0x259;
      var s26 := Swap(s25, 1);
      assert s26.stack[11] == 0x259;
      var s27 := Swap(s26, 4);
      assert s27.stack[11] == 0x259;
      var s28 := Add(s27);
      assert s28.stack[10] == 0x259;
      var s29 := Swap(s28, 5);
      assert s29.stack[10] == 0x259;
      var s30 := Pop(s29);
      assert s30.stack[9] == 0x259;
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s65(s31, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 221
    * Starting at 0x1482
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1482 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[9] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[8] == 0x259;
      var s3 := Pop(s2);
      assert s3.stack[7] == 0x259;
      var s4 := Dup(s3, 1);
      assert s4.stack[8] == 0x259;
      var s5 := Dup(s4, 4);
      assert s5.stack[9] == 0x259;
      var s6 := Sub(s5);
      assert s6.stack[8] == 0x259;
      var s7 := Dup(s6, 2);
      assert s7.stack[9] == 0x259;
      var s8 := Dup(s7, 6);
      assert s8.stack[10] == 0x259;
      var s9 := Gas(s8);
      assert s9.stack[11] == 0x259;
      var s10 := StaticCall(s9);
      assert s10.stack[6] == 0x259;
      var s11 := IsZero(s10);
      assert s11.stack[6] == 0x259;
      var s12 := Dup(s11, 1);
      assert s12.stack[7] == 0x259;
      var s13 := IsZero(s12);
      assert s13.stack[7] == 0x259;
      var s14 := PushN(s13, 2, 0x149c);
      assert s14.stack[0] == 0x149c;
      assert s14.stack[8] == 0x259;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s15, gas - 1)
      else
        ExecuteFromCFGNode_s66(s15, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 222
    * Starting at 0x1493
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1493 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.stack[7] == 0x259;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[8] == 0x259;
      var s3 := Dup(s2, 1);
      assert s3.stack[9] == 0x259;
      var s4 := ReturnDataCopy(s3);
      assert s4.stack[6] == 0x259;
      var s5 := ReturnDataSize(s4);
      assert s5.stack[7] == 0x259;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[8] == 0x259;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 67
    * Segment Id for this node is: 223
    * Starting at 0x149c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x149c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[5] == 0x259;
      var s3 := Pop(s2);
      assert s3.stack[4] == 0x259;
      var s4 := Pop(s3);
      assert s4.stack[3] == 0x259;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[4] == 0x259;
      var s6 := MLoad(s5);
      assert s6.stack[4] == 0x259;
      var s7 := ReturnDataSize(s6);
      assert s7.stack[5] == 0x259;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[6] == 0x259;
      var s9 := Dup(s8, 2);
      assert s9.stack[7] == 0x259;
      var s10 := Lt(s9);
      assert s10.stack[6] == 0x259;
      var s11 := IsZero(s10);
      assert s11.stack[6] == 0x259;
      var s12 := PushN(s11, 2, 0x14b1);
      assert s12.stack[0] == 0x14b1;
      assert s12.stack[7] == 0x259;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s13, gas - 1)
      else
        ExecuteFromCFGNode_s68(s13, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 224
    * Starting at 0x14ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[6] == 0x259;
      var s2 := Dup(s1, 1);
      assert s2.stack[7] == 0x259;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 69
    * Segment Id for this node is: 225
    * Starting at 0x14b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x259

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x259;
      var s2 := Pop(s1);
      assert s2.stack[4] == 0x259;
      var s3 := MLoad(s2);
      assert s3.stack[4] == 0x259;
      var s4 := Swap(s3, 3);
      assert s4.stack[4] == 0x259;
      var s5 := Pop(s4);
      assert s5.stack[3] == 0x259;
      var s6 := Pop(s5);
      assert s6.stack[2] == 0x259;
      var s7 := Pop(s6);
      assert s7.stack[1] == 0x259;
      var s8 := Swap(s7, 1);
      assert s8.stack[0] == 0x259;
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s9, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 46
    * Starting at 0x259
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x259 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := Dup(s2, 1);
      var s4 := MLoad(s3);
      var s5 := Swap(s4, 2);
      var s6 := Dup(s5, 3);
      var s7 := MStore(s6);
      var s8 := MLoad(s7);
      var s9 := Swap(s8, 1);
      var s10 := Dup(s9, 2);
      var s11 := Swap(s10, 1);
      var s12 := Sub(s11);
      var s13 := PushN(s12, 1, 0x20);
      var s14 := Add(s13);
      var s15 := Swap(s14, 1);
      var s16 := Return(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 71
    * Segment Id for this node is: 34
    * Starting at 0x1ba
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup(s2, 1);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x01c6);
      assert s5.stack[0] == 0x1c6;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s6, gas - 1)
      else
        ExecuteFromCFGNode_s72(s6, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 35
    * Starting at 0x1c2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Dup(s1, 1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 73
    * Segment Id for this node is: 36
    * Starting at 0x1c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x01cf);
      assert s3.stack[0] == 0x1cf;
      var s4 := PushN(s3, 2, 0x10b5);
      assert s4.stack[0] == 0x10b5;
      assert s4.stack[1] == 0x1cf;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s5, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 181
    * Starting at 0x10b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0x1cf;
      var s2 := PushN(s1, 1, 0x60);
      assert s2.stack[1] == 0x1cf;
      var s3 := PushN(s2, 2, 0x10c2);
      assert s3.stack[0] == 0x10c2;
      assert s3.stack[2] == 0x1cf;
      var s4 := PushN(s3, 1, 0x20);
      assert s4.stack[1] == 0x10c2;
      assert s4.stack[3] == 0x1cf;
      var s5 := SLoad(s4);
      assert s5.stack[1] == 0x10c2;
      assert s5.stack[3] == 0x1cf;
      var s6 := PushN(s5, 2, 0x14ba);
      assert s6.stack[0] == 0x14ba;
      assert s6.stack[2] == 0x10c2;
      assert s6.stack[4] == 0x1cf;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s7, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 226
    * Starting at 0x14ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x10c2

    requires s0.stack[3] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x10c2;
      assert s1.stack[3] == 0x1cf;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0x10c2;
      assert s2.stack[4] == 0x1cf;
      var s3 := Dup(s2, 1);
      assert s3.stack[3] == 0x10c2;
      assert s3.stack[5] == 0x1cf;
      var s4 := MLoad(s3);
      assert s4.stack[3] == 0x10c2;
      assert s4.stack[5] == 0x1cf;
      var s5 := PushN(s4, 1, 0x08);
      assert s5.stack[4] == 0x10c2;
      assert s5.stack[6] == 0x1cf;
      var s6 := Dup(s5, 1);
      assert s6.stack[5] == 0x10c2;
      assert s6.stack[7] == 0x1cf;
      var s7 := Dup(s6, 3);
      assert s7.stack[6] == 0x10c2;
      assert s7.stack[8] == 0x1cf;
      var s8 := MStore(s7);
      assert s8.stack[4] == 0x10c2;
      assert s8.stack[6] == 0x1cf;
      var s9 := Dup(s8, 2);
      assert s9.stack[5] == 0x10c2;
      assert s9.stack[7] == 0x1cf;
      var s10 := Dup(s9, 4);
      assert s10.stack[6] == 0x10c2;
      assert s10.stack[8] == 0x1cf;
      var s11 := Add(s10);
      assert s11.stack[5] == 0x10c2;
      assert s11.stack[7] == 0x1cf;
      var s12 := Swap(s11, 1);
      assert s12.stack[5] == 0x10c2;
      assert s12.stack[7] == 0x1cf;
      var s13 := Swap(s12, 3);
      assert s13.stack[5] == 0x10c2;
      assert s13.stack[7] == 0x1cf;
      var s14 := MStore(s13);
      assert s14.stack[3] == 0x10c2;
      assert s14.stack[5] == 0x1cf;
      var s15 := PushN(s14, 1, 0x60);
      assert s15.stack[4] == 0x10c2;
      assert s15.stack[6] == 0x1cf;
      var s16 := Swap(s15, 2);
      assert s16.stack[4] == 0x10c2;
      assert s16.stack[6] == 0x1cf;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[5] == 0x10c2;
      assert s17.stack[7] == 0x1cf;
      var s18 := Dup(s17, 3);
      assert s18.stack[6] == 0x10c2;
      assert s18.stack[8] == 0x1cf;
      var s19 := Add(s18);
      assert s19.stack[5] == 0x10c2;
      assert s19.stack[7] == 0x1cf;
      var s20 := Dup(s19, 2);
      assert s20.stack[6] == 0x10c2;
      assert s20.stack[8] == 0x1cf;
      var s21 := Dup(s20, 1);
      assert s21.stack[7] == 0x10c2;
      assert s21.stack[9] == 0x1cf;
      var s22 := CallDataSize(s21);
      assert s22.stack[8] == 0x10c2;
      assert s22.stack[10] == 0x1cf;
      var s23 := Dup(s22, 4);
      assert s23.stack[9] == 0x10c2;
      assert s23.stack[11] == 0x1cf;
      var s24 := CallDataCopy(s23);
      assert s24.stack[6] == 0x10c2;
      assert s24.stack[8] == 0x1cf;
      var s25 := Add(s24);
      assert s25.stack[5] == 0x10c2;
      assert s25.stack[7] == 0x1cf;
      var s26 := Swap(s25, 1);
      assert s26.stack[5] == 0x10c2;
      assert s26.stack[7] == 0x1cf;
      var s27 := Pop(s26);
      assert s27.stack[4] == 0x10c2;
      assert s27.stack[6] == 0x1cf;
      var s28 := Pop(s27);
      assert s28.stack[3] == 0x10c2;
      assert s28.stack[5] == 0x1cf;
      var s29 := Swap(s28, 1);
      assert s29.stack[3] == 0x10c2;
      assert s29.stack[5] == 0x1cf;
      var s30 := Pop(s29);
      assert s30.stack[2] == 0x10c2;
      assert s30.stack[4] == 0x1cf;
      var s31 := PushN(s30, 1, 0xc0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s76(s31, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 227
    * Starting at 0x14de
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x10c2

    requires s0.stack[5] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[4] == 0x10c2;
      assert s1.stack[6] == 0x1cf;
      var s2 := Swap(s1, 1);
      assert s2.stack[4] == 0x10c2;
      assert s2.stack[6] == 0x1cf;
      var s3 := Shl(s2);
      assert s3.stack[3] == 0x10c2;
      assert s3.stack[5] == 0x1cf;
      var s4 := Dup(s3, 1);
      assert s4.stack[4] == 0x10c2;
      assert s4.stack[6] == 0x1cf;
      var s5 := PushN(s4, 1, 0x07);
      assert s5.stack[5] == 0x10c2;
      assert s5.stack[7] == 0x1cf;
      var s6 := Byte(s5);
      assert s6.stack[4] == 0x10c2;
      assert s6.stack[6] == 0x1cf;
      var s7 := PushN(s6, 1, 0xf8);
      assert s7.stack[5] == 0x10c2;
      assert s7.stack[7] == 0x1cf;
      var s8 := Shl(s7);
      assert s8.stack[4] == 0x10c2;
      assert s8.stack[6] == 0x1cf;
      var s9 := Dup(s8, 3);
      assert s9.stack[5] == 0x10c2;
      assert s9.stack[7] == 0x1cf;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[6] == 0x10c2;
      assert s10.stack[8] == 0x1cf;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x10c2;
      assert s11.stack[9] == 0x1cf;
      var s12 := MLoad(s11);
      assert s12.stack[7] == 0x10c2;
      assert s12.stack[9] == 0x1cf;
      var s13 := Dup(s12, 2);
      assert s13.stack[8] == 0x10c2;
      assert s13.stack[10] == 0x1cf;
      var s14 := Lt(s13);
      assert s14.stack[7] == 0x10c2;
      assert s14.stack[9] == 0x1cf;
      var s15 := PushN(s14, 2, 0x14f4);
      assert s15.stack[0] == 0x14f4;
      assert s15.stack[8] == 0x10c2;
      assert s15.stack[10] == 0x1cf;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s16, gas - 1)
      else
        ExecuteFromCFGNode_s77(s16, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 228
    * Starting at 0x14f3
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 78
    * Segment Id for this node is: 229
    * Starting at 0x14f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x10c2;
      assert s1.stack[8] == 0x1cf;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x10c2;
      assert s2.stack[9] == 0x1cf;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x10c2;
      assert s3.stack[8] == 0x1cf;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x10c2;
      assert s4.stack[7] == 0x1cf;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x10c2;
      assert s5.stack[7] == 0x1cf;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x10c2;
      assert s6.stack[8] == 0x1cf;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x10c2;
      assert s7.stack[8] == 0x1cf;
      var s8 := And(s7);
      assert s8.stack[5] == 0x10c2;
      assert s8.stack[7] == 0x1cf;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x10c2;
      assert s9.stack[7] == 0x1cf;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x10c2;
      assert s10.stack[8] == 0x1cf;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x10c2;
      assert s11.stack[9] == 0x1cf;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x10c2;
      assert s12.stack[8] == 0x1cf;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x10c2;
      assert s13.stack[8] == 0x1cf;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x10c2;
      assert s14.stack[6] == 0x1cf;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x10c2;
      assert s15.stack[5] == 0x1cf;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x10c2;
      assert s16.stack[6] == 0x1cf;
      var s17 := PushN(s16, 1, 0x06);
      assert s17.stack[5] == 0x10c2;
      assert s17.stack[7] == 0x1cf;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x10c2;
      assert s18.stack[6] == 0x1cf;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x10c2;
      assert s19.stack[7] == 0x1cf;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x10c2;
      assert s20.stack[6] == 0x1cf;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x10c2;
      assert s21.stack[7] == 0x1cf;
      var s22 := PushN(s21, 1, 0x01);
      assert s22.stack[6] == 0x10c2;
      assert s22.stack[8] == 0x1cf;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x10c2;
      assert s23.stack[9] == 0x1cf;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x10c2;
      assert s24.stack[9] == 0x1cf;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x10c2;
      assert s25.stack[10] == 0x1cf;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x10c2;
      assert s26.stack[9] == 0x1cf;
      var s27 := PushN(s26, 2, 0x1537);
      assert s27.stack[0] == 0x1537;
      assert s27.stack[8] == 0x10c2;
      assert s27.stack[10] == 0x1cf;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s80(s28, gas - 1)
      else
        ExecuteFromCFGNode_s79(s28, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 230
    * Starting at 0x1536
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 80
    * Segment Id for this node is: 231
    * Starting at 0x1537
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1537 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x10c2;
      assert s1.stack[8] == 0x1cf;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x10c2;
      assert s2.stack[9] == 0x1cf;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x10c2;
      assert s3.stack[8] == 0x1cf;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x10c2;
      assert s4.stack[7] == 0x1cf;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x10c2;
      assert s5.stack[7] == 0x1cf;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x10c2;
      assert s6.stack[8] == 0x1cf;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x10c2;
      assert s7.stack[8] == 0x1cf;
      var s8 := And(s7);
      assert s8.stack[5] == 0x10c2;
      assert s8.stack[7] == 0x1cf;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x10c2;
      assert s9.stack[7] == 0x1cf;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x10c2;
      assert s10.stack[8] == 0x1cf;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x10c2;
      assert s11.stack[9] == 0x1cf;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x10c2;
      assert s12.stack[8] == 0x1cf;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x10c2;
      assert s13.stack[8] == 0x1cf;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x10c2;
      assert s14.stack[6] == 0x1cf;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x10c2;
      assert s15.stack[5] == 0x1cf;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x10c2;
      assert s16.stack[6] == 0x1cf;
      var s17 := PushN(s16, 1, 0x05);
      assert s17.stack[5] == 0x10c2;
      assert s17.stack[7] == 0x1cf;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x10c2;
      assert s18.stack[6] == 0x1cf;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x10c2;
      assert s19.stack[7] == 0x1cf;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x10c2;
      assert s20.stack[6] == 0x1cf;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x10c2;
      assert s21.stack[7] == 0x1cf;
      var s22 := PushN(s21, 1, 0x02);
      assert s22.stack[6] == 0x10c2;
      assert s22.stack[8] == 0x1cf;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x10c2;
      assert s23.stack[9] == 0x1cf;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x10c2;
      assert s24.stack[9] == 0x1cf;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x10c2;
      assert s25.stack[10] == 0x1cf;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x10c2;
      assert s26.stack[9] == 0x1cf;
      var s27 := PushN(s26, 2, 0x157a);
      assert s27.stack[0] == 0x157a;
      assert s27.stack[8] == 0x10c2;
      assert s27.stack[10] == 0x1cf;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s82(s28, gas - 1)
      else
        ExecuteFromCFGNode_s81(s28, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 232
    * Starting at 0x1579
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1579 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 82
    * Segment Id for this node is: 233
    * Starting at 0x157a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x10c2;
      assert s1.stack[8] == 0x1cf;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x10c2;
      assert s2.stack[9] == 0x1cf;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x10c2;
      assert s3.stack[8] == 0x1cf;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x10c2;
      assert s4.stack[7] == 0x1cf;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x10c2;
      assert s5.stack[7] == 0x1cf;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x10c2;
      assert s6.stack[8] == 0x1cf;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x10c2;
      assert s7.stack[8] == 0x1cf;
      var s8 := And(s7);
      assert s8.stack[5] == 0x10c2;
      assert s8.stack[7] == 0x1cf;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x10c2;
      assert s9.stack[7] == 0x1cf;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x10c2;
      assert s10.stack[8] == 0x1cf;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x10c2;
      assert s11.stack[9] == 0x1cf;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x10c2;
      assert s12.stack[8] == 0x1cf;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x10c2;
      assert s13.stack[8] == 0x1cf;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x10c2;
      assert s14.stack[6] == 0x1cf;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x10c2;
      assert s15.stack[5] == 0x1cf;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x10c2;
      assert s16.stack[6] == 0x1cf;
      var s17 := PushN(s16, 1, 0x04);
      assert s17.stack[5] == 0x10c2;
      assert s17.stack[7] == 0x1cf;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x10c2;
      assert s18.stack[6] == 0x1cf;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x10c2;
      assert s19.stack[7] == 0x1cf;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x10c2;
      assert s20.stack[6] == 0x1cf;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x10c2;
      assert s21.stack[7] == 0x1cf;
      var s22 := PushN(s21, 1, 0x03);
      assert s22.stack[6] == 0x10c2;
      assert s22.stack[8] == 0x1cf;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x10c2;
      assert s23.stack[9] == 0x1cf;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x10c2;
      assert s24.stack[9] == 0x1cf;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x10c2;
      assert s25.stack[10] == 0x1cf;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x10c2;
      assert s26.stack[9] == 0x1cf;
      var s27 := PushN(s26, 2, 0x15bd);
      assert s27.stack[0] == 0x15bd;
      assert s27.stack[8] == 0x10c2;
      assert s27.stack[10] == 0x1cf;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s28, gas - 1)
      else
        ExecuteFromCFGNode_s83(s28, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 234
    * Starting at 0x15bc
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 84
    * Segment Id for this node is: 235
    * Starting at 0x15bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x10c2;
      assert s1.stack[8] == 0x1cf;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x10c2;
      assert s2.stack[9] == 0x1cf;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x10c2;
      assert s3.stack[8] == 0x1cf;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x10c2;
      assert s4.stack[7] == 0x1cf;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x10c2;
      assert s5.stack[7] == 0x1cf;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x10c2;
      assert s6.stack[8] == 0x1cf;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x10c2;
      assert s7.stack[8] == 0x1cf;
      var s8 := And(s7);
      assert s8.stack[5] == 0x10c2;
      assert s8.stack[7] == 0x1cf;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x10c2;
      assert s9.stack[7] == 0x1cf;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x10c2;
      assert s10.stack[8] == 0x1cf;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x10c2;
      assert s11.stack[9] == 0x1cf;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x10c2;
      assert s12.stack[8] == 0x1cf;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x10c2;
      assert s13.stack[8] == 0x1cf;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x10c2;
      assert s14.stack[6] == 0x1cf;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x10c2;
      assert s15.stack[5] == 0x1cf;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x10c2;
      assert s16.stack[6] == 0x1cf;
      var s17 := PushN(s16, 1, 0x03);
      assert s17.stack[5] == 0x10c2;
      assert s17.stack[7] == 0x1cf;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x10c2;
      assert s18.stack[6] == 0x1cf;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x10c2;
      assert s19.stack[7] == 0x1cf;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x10c2;
      assert s20.stack[6] == 0x1cf;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x10c2;
      assert s21.stack[7] == 0x1cf;
      var s22 := PushN(s21, 1, 0x04);
      assert s22.stack[6] == 0x10c2;
      assert s22.stack[8] == 0x1cf;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x10c2;
      assert s23.stack[9] == 0x1cf;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x10c2;
      assert s24.stack[9] == 0x1cf;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x10c2;
      assert s25.stack[10] == 0x1cf;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x10c2;
      assert s26.stack[9] == 0x1cf;
      var s27 := PushN(s26, 2, 0x1600);
      assert s27.stack[0] == 0x1600;
      assert s27.stack[8] == 0x10c2;
      assert s27.stack[10] == 0x1cf;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s28, gas - 1)
      else
        ExecuteFromCFGNode_s85(s28, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 236
    * Starting at 0x15ff
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 86
    * Segment Id for this node is: 237
    * Starting at 0x1600
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1600 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x10c2;
      assert s1.stack[8] == 0x1cf;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x10c2;
      assert s2.stack[9] == 0x1cf;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x10c2;
      assert s3.stack[8] == 0x1cf;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x10c2;
      assert s4.stack[7] == 0x1cf;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x10c2;
      assert s5.stack[7] == 0x1cf;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x10c2;
      assert s6.stack[8] == 0x1cf;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x10c2;
      assert s7.stack[8] == 0x1cf;
      var s8 := And(s7);
      assert s8.stack[5] == 0x10c2;
      assert s8.stack[7] == 0x1cf;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x10c2;
      assert s9.stack[7] == 0x1cf;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x10c2;
      assert s10.stack[8] == 0x1cf;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x10c2;
      assert s11.stack[9] == 0x1cf;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x10c2;
      assert s12.stack[8] == 0x1cf;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x10c2;
      assert s13.stack[8] == 0x1cf;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x10c2;
      assert s14.stack[6] == 0x1cf;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x10c2;
      assert s15.stack[5] == 0x1cf;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x10c2;
      assert s16.stack[6] == 0x1cf;
      var s17 := PushN(s16, 1, 0x02);
      assert s17.stack[5] == 0x10c2;
      assert s17.stack[7] == 0x1cf;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x10c2;
      assert s18.stack[6] == 0x1cf;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x10c2;
      assert s19.stack[7] == 0x1cf;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x10c2;
      assert s20.stack[6] == 0x1cf;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x10c2;
      assert s21.stack[7] == 0x1cf;
      var s22 := PushN(s21, 1, 0x05);
      assert s22.stack[6] == 0x10c2;
      assert s22.stack[8] == 0x1cf;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x10c2;
      assert s23.stack[9] == 0x1cf;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x10c2;
      assert s24.stack[9] == 0x1cf;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x10c2;
      assert s25.stack[10] == 0x1cf;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x10c2;
      assert s26.stack[9] == 0x1cf;
      var s27 := PushN(s26, 2, 0x1643);
      assert s27.stack[0] == 0x1643;
      assert s27.stack[8] == 0x10c2;
      assert s27.stack[10] == 0x1cf;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s28, gas - 1)
      else
        ExecuteFromCFGNode_s87(s28, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 238
    * Starting at 0x1642
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1642 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 88
    * Segment Id for this node is: 239
    * Starting at 0x1643
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1643 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x10c2;
      assert s1.stack[8] == 0x1cf;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x10c2;
      assert s2.stack[9] == 0x1cf;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x10c2;
      assert s3.stack[8] == 0x1cf;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x10c2;
      assert s4.stack[7] == 0x1cf;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x10c2;
      assert s5.stack[7] == 0x1cf;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x10c2;
      assert s6.stack[8] == 0x1cf;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x10c2;
      assert s7.stack[8] == 0x1cf;
      var s8 := And(s7);
      assert s8.stack[5] == 0x10c2;
      assert s8.stack[7] == 0x1cf;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x10c2;
      assert s9.stack[7] == 0x1cf;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x10c2;
      assert s10.stack[8] == 0x1cf;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x10c2;
      assert s11.stack[9] == 0x1cf;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x10c2;
      assert s12.stack[8] == 0x1cf;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x10c2;
      assert s13.stack[8] == 0x1cf;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x10c2;
      assert s14.stack[6] == 0x1cf;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x10c2;
      assert s15.stack[5] == 0x1cf;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x10c2;
      assert s16.stack[6] == 0x1cf;
      var s17 := PushN(s16, 1, 0x01);
      assert s17.stack[5] == 0x10c2;
      assert s17.stack[7] == 0x1cf;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x10c2;
      assert s18.stack[6] == 0x1cf;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x10c2;
      assert s19.stack[7] == 0x1cf;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x10c2;
      assert s20.stack[6] == 0x1cf;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x10c2;
      assert s21.stack[7] == 0x1cf;
      var s22 := PushN(s21, 1, 0x06);
      assert s22.stack[6] == 0x10c2;
      assert s22.stack[8] == 0x1cf;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x10c2;
      assert s23.stack[9] == 0x1cf;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x10c2;
      assert s24.stack[9] == 0x1cf;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x10c2;
      assert s25.stack[10] == 0x1cf;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x10c2;
      assert s26.stack[9] == 0x1cf;
      var s27 := PushN(s26, 2, 0x1686);
      assert s27.stack[0] == 0x1686;
      assert s27.stack[8] == 0x10c2;
      assert s27.stack[10] == 0x1cf;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s28, gas - 1)
      else
        ExecuteFromCFGNode_s89(s28, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 240
    * Starting at 0x1685
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1685 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 90
    * Segment Id for this node is: 241
    * Starting at 0x1686
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1686 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x10c2;
      assert s1.stack[8] == 0x1cf;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x10c2;
      assert s2.stack[9] == 0x1cf;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x10c2;
      assert s3.stack[8] == 0x1cf;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x10c2;
      assert s4.stack[7] == 0x1cf;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x10c2;
      assert s5.stack[7] == 0x1cf;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x10c2;
      assert s6.stack[8] == 0x1cf;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x10c2;
      assert s7.stack[8] == 0x1cf;
      var s8 := And(s7);
      assert s8.stack[5] == 0x10c2;
      assert s8.stack[7] == 0x1cf;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x10c2;
      assert s9.stack[7] == 0x1cf;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x10c2;
      assert s10.stack[8] == 0x1cf;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x10c2;
      assert s11.stack[9] == 0x1cf;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x10c2;
      assert s12.stack[8] == 0x1cf;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x10c2;
      assert s13.stack[8] == 0x1cf;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x10c2;
      assert s14.stack[6] == 0x1cf;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x10c2;
      assert s15.stack[5] == 0x1cf;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x10c2;
      assert s16.stack[6] == 0x1cf;
      var s17 := PushN(s16, 1, 0x00);
      assert s17.stack[5] == 0x10c2;
      assert s17.stack[7] == 0x1cf;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x10c2;
      assert s18.stack[6] == 0x1cf;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x10c2;
      assert s19.stack[7] == 0x1cf;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x10c2;
      assert s20.stack[6] == 0x1cf;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x10c2;
      assert s21.stack[7] == 0x1cf;
      var s22 := PushN(s21, 1, 0x07);
      assert s22.stack[6] == 0x10c2;
      assert s22.stack[8] == 0x1cf;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x10c2;
      assert s23.stack[9] == 0x1cf;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x10c2;
      assert s24.stack[9] == 0x1cf;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x10c2;
      assert s25.stack[10] == 0x1cf;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x10c2;
      assert s26.stack[9] == 0x1cf;
      var s27 := PushN(s26, 2, 0x16c9);
      assert s27.stack[0] == 0x16c9;
      assert s27.stack[8] == 0x10c2;
      assert s27.stack[10] == 0x1cf;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s28, gas - 1)
      else
        ExecuteFromCFGNode_s91(s28, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 242
    * Starting at 0x16c8
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 92
    * Segment Id for this node is: 243
    * Starting at 0x16c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x10c2

    requires s0.stack[8] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x10c2;
      assert s1.stack[8] == 0x1cf;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x10c2;
      assert s2.stack[9] == 0x1cf;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x10c2;
      assert s3.stack[8] == 0x1cf;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x10c2;
      assert s4.stack[7] == 0x1cf;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x10c2;
      assert s5.stack[7] == 0x1cf;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x10c2;
      assert s6.stack[8] == 0x1cf;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x10c2;
      assert s7.stack[8] == 0x1cf;
      var s8 := And(s7);
      assert s8.stack[5] == 0x10c2;
      assert s8.stack[7] == 0x1cf;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x10c2;
      assert s9.stack[7] == 0x1cf;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x10c2;
      assert s10.stack[8] == 0x1cf;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x10c2;
      assert s11.stack[9] == 0x1cf;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x10c2;
      assert s12.stack[8] == 0x1cf;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x10c2;
      assert s13.stack[8] == 0x1cf;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x10c2;
      assert s14.stack[6] == 0x1cf;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x10c2;
      assert s15.stack[5] == 0x1cf;
      var s16 := Pop(s15);
      assert s16.stack[2] == 0x10c2;
      assert s16.stack[4] == 0x1cf;
      var s17 := Swap(s16, 2);
      assert s17.stack[0] == 0x10c2;
      assert s17.stack[4] == 0x1cf;
      var s18 := Swap(s17, 1);
      assert s18.stack[1] == 0x10c2;
      assert s18.stack[4] == 0x1cf;
      var s19 := Pop(s18);
      assert s19.stack[0] == 0x10c2;
      assert s19.stack[3] == 0x1cf;
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s20, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 182
    * Starting at 0x10c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1cf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x1cf;
      var s2 := Swap(s1, 1);
      assert s2.stack[2] == 0x1cf;
      var s3 := Pop(s2);
      assert s3.stack[1] == 0x1cf;
      var s4 := Swap(s3, 1);
      assert s4.stack[0] == 0x1cf;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s5, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 37
    * Starting at 0x1cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := Dup(s2, 1);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 3);
      var s8 := MStore(s7);
      var s9 := Dup(s8, 4);
      var s10 := MLoad(s9);
      var s11 := Dup(s10, 2);
      var s12 := Dup(s11, 4);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup(s14, 4);
      var s16 := MLoad(s15);
      var s17 := Swap(s16, 2);
      var s18 := Swap(s17, 3);
      var s19 := Dup(s18, 4);
      var s20 := Swap(s19, 3);
      var s21 := Swap(s20, 1);
      var s22 := Dup(s21, 4);
      var s23 := Add(s22);
      var s24 := Swap(s23, 2);
      var s25 := Dup(s24, 6);
      var s26 := Add(s25);
      var s27 := Swap(s26, 1);
      var s28 := Dup(s27, 1);
      var s29 := Dup(s28, 4);
      var s30 := Dup(s29, 4);
      var s31 := PushN(s30, 1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s95(s31, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 38
    * Starting at 0x1f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 4);
      var s3 := Dup(s2, 2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x0209);
      assert s6.stack[0] == 0x209;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s97(s7, gas - 1)
      else
        ExecuteFromCFGNode_s96(s7, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 39
    * Starting at 0x1fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := Dup(s1, 2);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 4);
      var s6 := Dup(s5, 3);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x20);
      var s10 := Add(s9);
      var s11 := PushN(s10, 2, 0x01f1);
      assert s11.stack[0] == 0x1f1;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s12, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 40
    * Starting at 0x209
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x209 as nat
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
      var s6 := Swap(s5, 1);
      var s7 := Pop(s6);
      var s8 := Swap(s7, 1);
      var s9 := Dup(s8, 2);
      var s10 := Add(s9);
      var s11 := Swap(s10, 1);
      var s12 := PushN(s11, 1, 0x1f);
      var s13 := And(s12);
      var s14 := Dup(s13, 1);
      var s15 := IsZero(s14);
      var s16 := PushN(s15, 2, 0x0236);
      assert s16.stack[0] == 0x236;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s99(s17, gas - 1)
      else
        ExecuteFromCFGNode_s98(s17, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 41
    * Starting at 0x21d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := Dup(s1, 3);
      var s3 := Sub(s2);
      var s4 := Dup(s3, 1);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 1, 0x01);
      var s7 := Dup(s6, 4);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := Sub(s8);
      var s10 := PushN(s9, 2, 0x0100);
      var s11 := Exp(s10);
      var s12 := Sub(s11);
      var s13 := Not(s12);
      var s14 := And(s13);
      var s15 := Dup(s14, 2);
      var s16 := MStore(s15);
      var s17 := PushN(s16, 1, 0x20);
      var s18 := Add(s17);
      var s19 := Swap(s18, 2);
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s99(s20, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 42
    * Starting at 0x236
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x236 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Swap(s2, 3);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 1, 0x40);
      var s8 := MLoad(s7);
      var s9 := Dup(s8, 1);
      var s10 := Swap(s9, 2);
      var s11 := Sub(s10);
      var s12 := Swap(s11, 1);
      var s13 := Return(s12);
      // Segment is terminal (Revert, Stop or Return)
      s13
  }

  /** Node 100
    * Segment Id for this node is: 12
    * Starting at 0xa4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x01b8);
      assert s2.stack[0] == 0x1b8;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[1] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[2] == 0x1b8;
      var s5 := CallDataSize(s4);
      assert s5.stack[3] == 0x1b8;
      var s6 := Sub(s5);
      assert s6.stack[2] == 0x1b8;
      var s7 := PushN(s6, 1, 0x80);
      assert s7.stack[3] == 0x1b8;
      var s8 := Dup(s7, 2);
      assert s8.stack[4] == 0x1b8;
      var s9 := Lt(s8);
      assert s9.stack[3] == 0x1b8;
      var s10 := IsZero(s9);
      assert s10.stack[3] == 0x1b8;
      var s11 := PushN(s10, 2, 0x00ba);
      assert s11.stack[0] == 0xba;
      assert s11.stack[4] == 0x1b8;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s12, gas - 1)
      else
        ExecuteFromCFGNode_s101(s12, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 13
    * Starting at 0xb6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[3] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[4] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 102
    * Segment Id for this node is: 14
    * Starting at 0xba
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x1b8;
      var s2 := Dup(s1, 2);
      assert s2.stack[3] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[2] == 0x1b8;
      var s4 := Swap(s3, 1);
      assert s4.stack[2] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[3] == 0x1b8;
      var s6 := Dup(s5, 2);
      assert s6.stack[4] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[3] == 0x1b8;
      var s8 := Dup(s7, 2);
      assert s8.stack[4] == 0x1b8;
      var s9 := CallDataLoad(s8);
      assert s9.stack[4] == 0x1b8;
      var s10 := PushN(s9, 5, 0x0100000000);
      assert s10.stack[5] == 0x1b8;
      var s11 := Dup(s10, 2);
      assert s11.stack[6] == 0x1b8;
      var s12 := Gt(s11);
      assert s12.stack[5] == 0x1b8;
      var s13 := IsZero(s12);
      assert s13.stack[5] == 0x1b8;
      var s14 := PushN(s13, 2, 0x00d5);
      assert s14.stack[0] == 0xd5;
      assert s14.stack[6] == 0x1b8;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s104(s15, gas - 1)
      else
        ExecuteFromCFGNode_s103(s15, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 15
    * Starting at 0xd1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 104
    * Segment Id for this node is: 16
    * Starting at 0xd5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x1b8;
      var s2 := Dup(s1, 3);
      assert s2.stack[5] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[4] == 0x1b8;
      var s4 := Dup(s3, 4);
      assert s4.stack[5] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[6] == 0x1b8;
      var s6 := Dup(s5, 3);
      assert s6.stack[7] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[6] == 0x1b8;
      var s8 := Gt(s7);
      assert s8.stack[5] == 0x1b8;
      var s9 := IsZero(s8);
      assert s9.stack[5] == 0x1b8;
      var s10 := PushN(s9, 2, 0x00e7);
      assert s10.stack[0] == 0xe7;
      assert s10.stack[6] == 0x1b8;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s11, gas - 1)
      else
        ExecuteFromCFGNode_s105(s11, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 17
    * Starting at 0xe3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 106
    * Segment Id for this node is: 18
    * Starting at 0xe7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[5] == 0x1b8;
      var s3 := CallDataLoad(s2);
      assert s3.stack[5] == 0x1b8;
      var s4 := Swap(s3, 1);
      assert s4.stack[5] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[6] == 0x1b8;
      var s6 := Add(s5);
      assert s6.stack[5] == 0x1b8;
      var s7 := Swap(s6, 2);
      assert s7.stack[5] == 0x1b8;
      var s8 := Dup(s7, 5);
      assert s8.stack[6] == 0x1b8;
      var s9 := PushN(s8, 1, 0x01);
      assert s9.stack[7] == 0x1b8;
      var s10 := Dup(s9, 4);
      assert s10.stack[8] == 0x1b8;
      var s11 := Mul(s10);
      assert s11.stack[7] == 0x1b8;
      var s12 := Dup(s11, 5);
      assert s12.stack[8] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[7] == 0x1b8;
      var s14 := Gt(s13);
      assert s14.stack[6] == 0x1b8;
      var s15 := PushN(s14, 5, 0x0100000000);
      assert s15.stack[7] == 0x1b8;
      var s16 := Dup(s15, 4);
      assert s16.stack[8] == 0x1b8;
      var s17 := Gt(s16);
      assert s17.stack[7] == 0x1b8;
      var s18 := Or(s17);
      assert s18.stack[6] == 0x1b8;
      var s19 := IsZero(s18);
      assert s19.stack[6] == 0x1b8;
      var s20 := PushN(s19, 2, 0x0109);
      assert s20.stack[0] == 0x109;
      assert s20.stack[7] == 0x1b8;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s21, gas - 1)
      else
        ExecuteFromCFGNode_s107(s21, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 19
    * Starting at 0x105
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[6] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[7] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 108
    * Segment Id for this node is: 20
    * Starting at 0x109
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x1b8;
      var s2 := Swap(s1, 2);
      assert s2.stack[5] == 0x1b8;
      var s3 := Swap(s2, 4);
      assert s3.stack[5] == 0x1b8;
      var s4 := Swap(s3, 1);
      assert s4.stack[5] == 0x1b8;
      var s5 := Swap(s4, 3);
      assert s5.stack[5] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[5] == 0x1b8;
      var s7 := Swap(s6, 2);
      assert s7.stack[5] == 0x1b8;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[6] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[7] == 0x1b8;
      var s10 := Add(s9);
      assert s10.stack[6] == 0x1b8;
      var s11 := Swap(s10, 1);
      assert s11.stack[6] == 0x1b8;
      var s12 := CallDataLoad(s11);
      assert s12.stack[6] == 0x1b8;
      var s13 := PushN(s12, 5, 0x0100000000);
      assert s13.stack[7] == 0x1b8;
      var s14 := Dup(s13, 2);
      assert s14.stack[8] == 0x1b8;
      var s15 := Gt(s14);
      assert s15.stack[7] == 0x1b8;
      var s16 := IsZero(s15);
      assert s16.stack[7] == 0x1b8;
      var s17 := PushN(s16, 2, 0x0127);
      assert s17.stack[0] == 0x127;
      assert s17.stack[8] == 0x1b8;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s18, gas - 1)
      else
        ExecuteFromCFGNode_s109(s18, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 21
    * Starting at 0x123
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[7] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[8] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 110
    * Segment Id for this node is: 22
    * Starting at 0x127
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x1b8;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x1b8;
      var s4 := Dup(s3, 4);
      assert s4.stack[7] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[8] == 0x1b8;
      var s6 := Dup(s5, 3);
      assert s6.stack[9] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[8] == 0x1b8;
      var s8 := Gt(s7);
      assert s8.stack[7] == 0x1b8;
      var s9 := IsZero(s8);
      assert s9.stack[7] == 0x1b8;
      var s10 := PushN(s9, 2, 0x0139);
      assert s10.stack[0] == 0x139;
      assert s10.stack[8] == 0x1b8;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s112(s11, gas - 1)
      else
        ExecuteFromCFGNode_s111(s11, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 23
    * Starting at 0x135
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[7] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[8] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 112
    * Segment Id for this node is: 24
    * Starting at 0x139
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[7] == 0x1b8;
      var s3 := CallDataLoad(s2);
      assert s3.stack[7] == 0x1b8;
      var s4 := Swap(s3, 1);
      assert s4.stack[7] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[8] == 0x1b8;
      var s6 := Add(s5);
      assert s6.stack[7] == 0x1b8;
      var s7 := Swap(s6, 2);
      assert s7.stack[7] == 0x1b8;
      var s8 := Dup(s7, 5);
      assert s8.stack[8] == 0x1b8;
      var s9 := PushN(s8, 1, 0x01);
      assert s9.stack[9] == 0x1b8;
      var s10 := Dup(s9, 4);
      assert s10.stack[10] == 0x1b8;
      var s11 := Mul(s10);
      assert s11.stack[9] == 0x1b8;
      var s12 := Dup(s11, 5);
      assert s12.stack[10] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[9] == 0x1b8;
      var s14 := Gt(s13);
      assert s14.stack[8] == 0x1b8;
      var s15 := PushN(s14, 5, 0x0100000000);
      assert s15.stack[9] == 0x1b8;
      var s16 := Dup(s15, 4);
      assert s16.stack[10] == 0x1b8;
      var s17 := Gt(s16);
      assert s17.stack[9] == 0x1b8;
      var s18 := Or(s17);
      assert s18.stack[8] == 0x1b8;
      var s19 := IsZero(s18);
      assert s19.stack[8] == 0x1b8;
      var s20 := PushN(s19, 2, 0x015b);
      assert s20.stack[0] == 0x15b;
      assert s20.stack[9] == 0x1b8;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s21, gas - 1)
      else
        ExecuteFromCFGNode_s113(s21, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 25
    * Starting at 0x157
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[8] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[9] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 114
    * Segment Id for this node is: 26
    * Starting at 0x15b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x1b8;
      var s2 := Swap(s1, 2);
      assert s2.stack[7] == 0x1b8;
      var s3 := Swap(s2, 4);
      assert s3.stack[7] == 0x1b8;
      var s4 := Swap(s3, 1);
      assert s4.stack[7] == 0x1b8;
      var s5 := Swap(s4, 3);
      assert s5.stack[7] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[7] == 0x1b8;
      var s7 := Swap(s6, 2);
      assert s7.stack[7] == 0x1b8;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[8] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[9] == 0x1b8;
      var s10 := Add(s9);
      assert s10.stack[8] == 0x1b8;
      var s11 := Swap(s10, 1);
      assert s11.stack[8] == 0x1b8;
      var s12 := CallDataLoad(s11);
      assert s12.stack[8] == 0x1b8;
      var s13 := PushN(s12, 5, 0x0100000000);
      assert s13.stack[9] == 0x1b8;
      var s14 := Dup(s13, 2);
      assert s14.stack[10] == 0x1b8;
      var s15 := Gt(s14);
      assert s15.stack[9] == 0x1b8;
      var s16 := IsZero(s15);
      assert s16.stack[9] == 0x1b8;
      var s17 := PushN(s16, 2, 0x0179);
      assert s17.stack[0] == 0x179;
      assert s17.stack[10] == 0x1b8;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s116(s18, gas - 1)
      else
        ExecuteFromCFGNode_s115(s18, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 27
    * Starting at 0x175
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x175 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[9] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[10] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 116
    * Segment Id for this node is: 28
    * Starting at 0x179
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x179 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0x1b8;
      var s2 := Dup(s1, 3);
      assert s2.stack[9] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[8] == 0x1b8;
      var s4 := Dup(s3, 4);
      assert s4.stack[9] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[10] == 0x1b8;
      var s6 := Dup(s5, 3);
      assert s6.stack[11] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[10] == 0x1b8;
      var s8 := Gt(s7);
      assert s8.stack[9] == 0x1b8;
      var s9 := IsZero(s8);
      assert s9.stack[9] == 0x1b8;
      var s10 := PushN(s9, 2, 0x018b);
      assert s10.stack[0] == 0x18b;
      assert s10.stack[10] == 0x1b8;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s11, gas - 1)
      else
        ExecuteFromCFGNode_s117(s11, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 29
    * Starting at 0x187
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x187 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[9] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[10] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 118
    * Segment Id for this node is: 30
    * Starting at 0x18b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[9] == 0x1b8;
      var s3 := CallDataLoad(s2);
      assert s3.stack[9] == 0x1b8;
      var s4 := Swap(s3, 1);
      assert s4.stack[9] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[10] == 0x1b8;
      var s6 := Add(s5);
      assert s6.stack[9] == 0x1b8;
      var s7 := Swap(s6, 2);
      assert s7.stack[9] == 0x1b8;
      var s8 := Dup(s7, 5);
      assert s8.stack[10] == 0x1b8;
      var s9 := PushN(s8, 1, 0x01);
      assert s9.stack[11] == 0x1b8;
      var s10 := Dup(s9, 4);
      assert s10.stack[12] == 0x1b8;
      var s11 := Mul(s10);
      assert s11.stack[11] == 0x1b8;
      var s12 := Dup(s11, 5);
      assert s12.stack[12] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[11] == 0x1b8;
      var s14 := Gt(s13);
      assert s14.stack[10] == 0x1b8;
      var s15 := PushN(s14, 5, 0x0100000000);
      assert s15.stack[11] == 0x1b8;
      var s16 := Dup(s15, 4);
      assert s16.stack[12] == 0x1b8;
      var s17 := Gt(s16);
      assert s17.stack[11] == 0x1b8;
      var s18 := Or(s17);
      assert s18.stack[10] == 0x1b8;
      var s19 := IsZero(s18);
      assert s19.stack[10] == 0x1b8;
      var s20 := PushN(s19, 2, 0x01ad);
      assert s20.stack[0] == 0x1ad;
      assert s20.stack[11] == 0x1b8;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s120(s21, gas - 1)
      else
        ExecuteFromCFGNode_s119(s21, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 31
    * Starting at 0x1a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[10] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[11] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 120
    * Segment Id for this node is: 32
    * Starting at 0x1ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[9] == 0x1b8;
      var s2 := Swap(s1, 2);
      assert s2.stack[9] == 0x1b8;
      var s3 := Swap(s2, 4);
      assert s3.stack[9] == 0x1b8;
      var s4 := Pop(s3);
      assert s4.stack[8] == 0x1b8;
      var s5 := Swap(s4, 2);
      assert s5.stack[8] == 0x1b8;
      var s6 := Pop(s5);
      assert s6.stack[7] == 0x1b8;
      var s7 := CallDataLoad(s6);
      assert s7.stack[7] == 0x1b8;
      var s8 := PushN(s7, 2, 0x0304);
      assert s8.stack[0] == 0x304;
      assert s8.stack[8] == 0x1b8;
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s9, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 50
    * Starting at 0x304
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x1b8;
      var s2 := PushN(s1, 1, 0x30);
      assert s2.stack[8] == 0x1b8;
      var s3 := Dup(s2, 7);
      assert s3.stack[9] == 0x1b8;
      var s4 := Eq(s3);
      assert s4.stack[8] == 0x1b8;
      var s5 := PushN(s4, 2, 0x035d);
      assert s5.stack[0] == 0x35d;
      assert s5.stack[9] == 0x1b8;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s124(s6, gas - 1)
      else
        ExecuteFromCFGNode_s122(s6, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 51
    * Starting at 0x30d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[8] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[8] == 0x1b8;
      var s3 := PushN(s2, 32, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      assert s3.stack[9] == 0x1b8;
      var s4 := Dup(s3, 2);
      assert s4.stack[10] == 0x1b8;
      var s5 := MStore(s4);
      assert s5.stack[8] == 0x1b8;
      var s6 := PushN(s5, 1, 0x04);
      assert s6.stack[9] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[8] == 0x1b8;
      var s8 := Dup(s7, 1);
      assert s8.stack[9] == 0x1b8;
      var s9 := Dup(s8, 1);
      assert s9.stack[10] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[11] == 0x1b8;
      var s11 := Add(s10);
      assert s11.stack[10] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[11] == 0x1b8;
      var s13 := Dup(s12, 2);
      assert s13.stack[12] == 0x1b8;
      var s14 := Sub(s13);
      assert s14.stack[11] == 0x1b8;
      var s15 := Dup(s14, 3);
      assert s15.stack[12] == 0x1b8;
      var s16 := MStore(s15);
      assert s16.stack[10] == 0x1b8;
      var s17 := PushN(s16, 1, 0x26);
      assert s17.stack[11] == 0x1b8;
      var s18 := Dup(s17, 2);
      assert s18.stack[12] == 0x1b8;
      var s19 := MStore(s18);
      assert s19.stack[10] == 0x1b8;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[11] == 0x1b8;
      var s21 := Add(s20);
      assert s21.stack[10] == 0x1b8;
      var s22 := Dup(s21, 1);
      assert s22.stack[11] == 0x1b8;
      var s23 := PushN(s22, 2, 0x1805);
      assert s23.stack[12] == 0x1b8;
      var s24 := PushN(s23, 1, 0x26);
      assert s24.stack[13] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[13] == 0x1b8;
      var s26 := CodeCopy(s25); 
      assert s26.stack[10] == 0x1b8;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[11] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[10] == 0x1b8;
      var s29 := Swap(s28, 2);
      assert s29.stack[10] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[9] == 0x1b8;
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s123(s31, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 52
    * Starting at 0x355
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x355 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[9] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[9] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x1b8;
      var s4 := Swap(s3, 2);
      assert s4.stack[10] == 0x1b8;
      var s5 := Sub(s4);
      assert s5.stack[9] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[9] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 124
    * Segment Id for this node is: 53
    * Starting at 0x35d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[8] == 0x1b8;
      var s3 := Dup(s2, 5);
      assert s3.stack[9] == 0x1b8;
      var s4 := Eq(s3);
      assert s4.stack[8] == 0x1b8;
      var s5 := PushN(s4, 2, 0x03b6);
      assert s5.stack[0] == 0x3b6;
      assert s5.stack[9] == 0x1b8;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s6, gas - 1)
      else
        ExecuteFromCFGNode_s125(s6, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 54
    * Starting at 0x366
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x366 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[8] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[8] == 0x1b8;
      var s3 := PushN(s2, 32, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      assert s3.stack[9] == 0x1b8;
      var s4 := Dup(s3, 2);
      assert s4.stack[10] == 0x1b8;
      var s5 := MStore(s4);
      assert s5.stack[8] == 0x1b8;
      var s6 := PushN(s5, 1, 0x04);
      assert s6.stack[9] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[8] == 0x1b8;
      var s8 := Dup(s7, 1);
      assert s8.stack[9] == 0x1b8;
      var s9 := Dup(s8, 1);
      assert s9.stack[10] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[11] == 0x1b8;
      var s11 := Add(s10);
      assert s11.stack[10] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[11] == 0x1b8;
      var s13 := Dup(s12, 2);
      assert s13.stack[12] == 0x1b8;
      var s14 := Sub(s13);
      assert s14.stack[11] == 0x1b8;
      var s15 := Dup(s14, 3);
      assert s15.stack[12] == 0x1b8;
      var s16 := MStore(s15);
      assert s16.stack[10] == 0x1b8;
      var s17 := PushN(s16, 1, 0x36);
      assert s17.stack[11] == 0x1b8;
      var s18 := Dup(s17, 2);
      assert s18.stack[12] == 0x1b8;
      var s19 := MStore(s18);
      assert s19.stack[10] == 0x1b8;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[11] == 0x1b8;
      var s21 := Add(s20);
      assert s21.stack[10] == 0x1b8;
      var s22 := Dup(s21, 1);
      assert s22.stack[11] == 0x1b8;
      var s23 := PushN(s22, 2, 0x179c);
      assert s23.stack[12] == 0x1b8;
      var s24 := PushN(s23, 1, 0x36);
      assert s24.stack[13] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[13] == 0x1b8;
      var s26 := CodeCopy(s25);
      assert s26.stack[10] == 0x1b8;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[11] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[10] == 0x1b8;
      var s29 := Swap(s28, 2);
      assert s29.stack[10] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[9] == 0x1b8;
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s126(s31, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 55
    * Starting at 0x3ae
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[9] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[9] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x1b8;
      var s4 := Swap(s3, 2);
      assert s4.stack[10] == 0x1b8;
      var s5 := Sub(s4);
      assert s5.stack[9] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[9] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 127
    * Segment Id for this node is: 56
    * Starting at 0x3b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x1b8;
      var s2 := PushN(s1, 1, 0x60);
      assert s2.stack[8] == 0x1b8;
      var s3 := Dup(s2, 3);
      assert s3.stack[9] == 0x1b8;
      var s4 := Eq(s3);
      assert s4.stack[8] == 0x1b8;
      var s5 := PushN(s4, 2, 0x040f);
      assert s5.stack[0] == 0x40f;
      assert s5.stack[9] == 0x1b8;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s6, gas - 1)
      else
        ExecuteFromCFGNode_s128(s6, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 57
    * Starting at 0x3bf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[8] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[8] == 0x1b8;
      var s3 := PushN(s2, 32, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      assert s3.stack[9] == 0x1b8;
      var s4 := Dup(s3, 2);
      assert s4.stack[10] == 0x1b8;
      var s5 := MStore(s4);
      assert s5.stack[8] == 0x1b8;
      var s6 := PushN(s5, 1, 0x04);
      assert s6.stack[9] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[8] == 0x1b8;
      var s8 := Dup(s7, 1);
      assert s8.stack[9] == 0x1b8;
      var s9 := Dup(s8, 1);
      assert s9.stack[10] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[11] == 0x1b8;
      var s11 := Add(s10);
      assert s11.stack[10] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[11] == 0x1b8;
      var s13 := Dup(s12, 2);
      assert s13.stack[12] == 0x1b8;
      var s14 := Sub(s13);
      assert s14.stack[11] == 0x1b8;
      var s15 := Dup(s14, 3);
      assert s15.stack[12] == 0x1b8;
      var s16 := MStore(s15);
      assert s16.stack[10] == 0x1b8;
      var s17 := PushN(s16, 1, 0x29);
      assert s17.stack[11] == 0x1b8;
      var s18 := Dup(s17, 2);
      assert s18.stack[12] == 0x1b8;
      var s19 := MStore(s18);
      assert s19.stack[10] == 0x1b8;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[11] == 0x1b8;
      var s21 := Add(s20);
      assert s21.stack[10] == 0x1b8;
      var s22 := Dup(s21, 1);
      assert s22.stack[11] == 0x1b8;
      var s23 := PushN(s22, 2, 0x1878);
      assert s23.stack[12] == 0x1b8;
      var s24 := PushN(s23, 1, 0x29);
      assert s24.stack[13] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[13] == 0x1b8;
      var s26 := CodeCopy(s25);
      assert s26.stack[10] == 0x1b8;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[11] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[10] == 0x1b8;
      var s29 := Swap(s28, 2);
      assert s29.stack[10] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[9] == 0x1b8;
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s129(s31, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 58
    * Starting at 0x407
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x407 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[9] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[9] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x1b8;
      var s4 := Swap(s3, 2);
      assert s4.stack[10] == 0x1b8;
      var s5 := Sub(s4);
      assert s5.stack[9] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[9] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 130
    * Segment Id for this node is: 59
    * Starting at 0x40f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x1b8;
      var s2 := PushN(s1, 8, 0x0de0b6b3a7640000);
      assert s2.stack[8] == 0x1b8;
      var s3 := CallValue(s2);
      assert s3.stack[9] == 0x1b8;
      var s4 := Lt(s3);
      assert s4.stack[8] == 0x1b8;
      var s5 := IsZero(s4);
      assert s5.stack[8] == 0x1b8;
      var s6 := PushN(s5, 2, 0x0470);
      assert s6.stack[0] == 0x470;
      assert s6.stack[9] == 0x1b8;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s7, gas - 1)
      else
        ExecuteFromCFGNode_s131(s7, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 60
    * Starting at 0x420
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x420 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[8] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[8] == 0x1b8;
      var s3 := PushN(s2, 32, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      assert s3.stack[9] == 0x1b8;
      var s4 := Dup(s3, 2);
      assert s4.stack[10] == 0x1b8;
      var s5 := MStore(s4);
      assert s5.stack[8] == 0x1b8;
      var s6 := PushN(s5, 1, 0x04);
      assert s6.stack[9] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[8] == 0x1b8;
      var s8 := Dup(s7, 1);
      assert s8.stack[9] == 0x1b8;
      var s9 := Dup(s8, 1);
      assert s9.stack[10] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[11] == 0x1b8;
      var s11 := Add(s10);
      assert s11.stack[10] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[11] == 0x1b8;
      var s13 := Dup(s12, 2);
      assert s13.stack[12] == 0x1b8;
      var s14 := Sub(s13);
      assert s14.stack[11] == 0x1b8;
      var s15 := Dup(s14, 3);
      assert s15.stack[12] == 0x1b8;
      var s16 := MStore(s15);
      assert s16.stack[10] == 0x1b8;
      var s17 := PushN(s16, 1, 0x26);
      assert s17.stack[11] == 0x1b8;
      var s18 := Dup(s17, 2);
      assert s18.stack[12] == 0x1b8;
      var s19 := MStore(s18);
      assert s19.stack[10] == 0x1b8;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[11] == 0x1b8;
      var s21 := Add(s20);
      assert s21.stack[10] == 0x1b8;
      var s22 := Dup(s21, 1);
      assert s22.stack[11] == 0x1b8;
      var s23 := PushN(s22, 2, 0x1852);
      assert s23.stack[12] == 0x1b8;
      var s24 := PushN(s23, 1, 0x26);
      assert s24.stack[13] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[13] == 0x1b8;
      var s26 := CodeCopy(s25);
      assert s26.stack[10] == 0x1b8;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[11] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[10] == 0x1b8;
      var s29 := Swap(s28, 2);
      assert s29.stack[10] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[9] == 0x1b8;
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s132(s31, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 61
    * Starting at 0x468
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x468 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[9] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[9] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x1b8;
      var s4 := Swap(s3, 2);
      assert s4.stack[10] == 0x1b8;
      var s5 := Sub(s4);
      assert s5.stack[9] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[9] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 133
    * Segment Id for this node is: 62
    * Starting at 0x470
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x470 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x1b8;
      var s2 := PushN(s1, 4, 0x3b9aca00);
      assert s2.stack[8] == 0x1b8;
      var s3 := CallValue(s2);
      assert s3.stack[9] == 0x1b8;
      var s4 := Mod(s3); 
      assert s4.stack[8] == 0x1b8;
      var s5 := IsZero(s4);
      assert s5.stack[8] == 0x1b8;
      var s6 := PushN(s5, 2, 0x04cd);
      assert s6.stack[0] == 0x4cd;
      assert s6.stack[9] == 0x1b8;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s7, gas - 1)
      else
        ExecuteFromCFGNode_s134(s7, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 63
    * Starting at 0x47d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[8] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[8] == 0x1b8;
      var s3 := PushN(s2, 32, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      assert s3.stack[9] == 0x1b8;
      var s4 := Dup(s3, 2);
      assert s4.stack[10] == 0x1b8;
      var s5 := MStore(s4);
      assert s5.stack[8] == 0x1b8;
      var s6 := PushN(s5, 1, 0x04);
      assert s6.stack[9] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[8] == 0x1b8;
      var s8 := Dup(s7, 1);
      assert s8.stack[9] == 0x1b8;
      var s9 := Dup(s8, 1);
      assert s9.stack[10] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[11] == 0x1b8;
      var s11 := Add(s10);
      assert s11.stack[10] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[11] == 0x1b8;
      var s13 := Dup(s12, 2);
      assert s13.stack[12] == 0x1b8;
      var s14 := Sub(s13);
      assert s14.stack[11] == 0x1b8;
      var s15 := Dup(s14, 3);
      assert s15.stack[12] == 0x1b8;
      var s16 := MStore(s15);
      assert s16.stack[10] == 0x1b8;
      var s17 := PushN(s16, 1, 0x33);
      assert s17.stack[11] == 0x1b8;
      var s18 := Dup(s17, 2);
      assert s18.stack[12] == 0x1b8;
      var s19 := MStore(s18);
      assert s19.stack[10] == 0x1b8;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[11] == 0x1b8;
      var s21 := Add(s20);
      assert s21.stack[10] == 0x1b8;
      var s22 := Dup(s21, 1);
      assert s22.stack[11] == 0x1b8;
      var s23 := PushN(s22, 2, 0x17d2);
      assert s23.stack[12] == 0x1b8;
      var s24 := PushN(s23, 1, 0x33);
      assert s24.stack[13] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[13] == 0x1b8;
      var s26 := CodeCopy(s25);
      assert s26.stack[10] == 0x1b8;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[11] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[10] == 0x1b8;
      var s29 := Swap(s28, 2);
      assert s29.stack[10] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[9] == 0x1b8;
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s135(s31, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 64
    * Starting at 0x4c5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[9] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[9] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[10] == 0x1b8;
      var s4 := Swap(s3, 2);
      assert s4.stack[10] == 0x1b8;
      var s5 := Sub(s4);
      assert s5.stack[9] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[9] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 136
    * Segment Id for this node is: 65
    * Starting at 0x4cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[7] == 0x1b8;
      var s2 := PushN(s1, 4, 0x3b9aca00);
      assert s2.stack[8] == 0x1b8;
      var s3 := CallValue(s2);
      assert s3.stack[9] == 0x1b8;
      var s4 := Div(s3);
      assert s4.stack[8] == 0x1b8;
      var s5 := PushN(s4, 8, 0xffffffffffffffff);
      assert s5.stack[9] == 0x1b8;
      var s6 := Dup(s5, 2);
      assert s6.stack[10] == 0x1b8;
      var s7 := Gt(s6);
      assert s7.stack[9] == 0x1b8;
      var s8 := IsZero(s7);
      assert s8.stack[9] == 0x1b8;
      var s9 := PushN(s8, 2, 0x0535);
      assert s9.stack[0] == 0x535;
      assert s9.stack[10] == 0x1b8;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s10, gas - 1)
      else
        ExecuteFromCFGNode_s137(s10, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 66
    * Starting at 0x4e5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[9] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[9] == 0x1b8;
      var s3 := PushN(s2, 32, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      assert s3.stack[10] == 0x1b8;
      var s4 := Dup(s3, 2);
      assert s4.stack[11] == 0x1b8;
      var s5 := MStore(s4);
      assert s5.stack[9] == 0x1b8;
      var s6 := PushN(s5, 1, 0x04);
      assert s6.stack[10] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[9] == 0x1b8;
      var s8 := Dup(s7, 1);
      assert s8.stack[10] == 0x1b8;
      var s9 := Dup(s8, 1);
      assert s9.stack[11] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[12] == 0x1b8;
      var s11 := Add(s10);
      assert s11.stack[11] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[12] == 0x1b8;
      var s13 := Dup(s12, 2);
      assert s13.stack[13] == 0x1b8;
      var s14 := Sub(s13);
      assert s14.stack[12] == 0x1b8;
      var s15 := Dup(s14, 3);
      assert s15.stack[13] == 0x1b8;
      var s16 := MStore(s15);
      assert s16.stack[11] == 0x1b8;
      var s17 := PushN(s16, 1, 0x27);
      assert s17.stack[12] == 0x1b8;
      var s18 := Dup(s17, 2);
      assert s18.stack[13] == 0x1b8;
      var s19 := MStore(s18);
      assert s19.stack[11] == 0x1b8;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[12] == 0x1b8;
      var s21 := Add(s20);
      assert s21.stack[11] == 0x1b8;
      var s22 := Dup(s21, 1);
      assert s22.stack[12] == 0x1b8;
      var s23 := PushN(s22, 2, 0x182b);
      assert s23.stack[13] == 0x1b8;
      var s24 := PushN(s23, 1, 0x27);
      assert s24.stack[14] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[14] == 0x1b8;
      var s26 := CodeCopy(s25);
      assert s26.stack[11] == 0x1b8;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[12] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[11] == 0x1b8;
      var s29 := Swap(s28, 2);
      assert s29.stack[11] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[10] == 0x1b8;
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s138(s31, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 67
    * Starting at 0x52d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[10] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[10] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[11] == 0x1b8;
      var s4 := Swap(s3, 2);
      assert s4.stack[11] == 0x1b8;
      var s5 := Sub(s4);
      assert s5.stack[10] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[10] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 139
    * Segment Id for this node is: 68
    * Starting at 0x535
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x535 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0x1b8;
      var s2 := PushN(s1, 1, 0x60);
      assert s2.stack[9] == 0x1b8;
      var s3 := PushN(s2, 2, 0x0540);
      assert s3.stack[0] == 0x540;
      assert s3.stack[10] == 0x1b8;
      var s4 := Dup(s3, 3);
      assert s4.stack[1] == 0x540;
      assert s4.stack[11] == 0x1b8;
      var s5 := PushN(s4, 2, 0x14ba);
      assert s5.stack[0] == 0x14ba;
      assert s5.stack[2] == 0x540;
      assert s5.stack[12] == 0x1b8;
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s6, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 226
    * Starting at 0x14ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x540

    requires s0.stack[11] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x540;
      assert s1.stack[11] == 0x1b8;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0x540;
      assert s2.stack[12] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[3] == 0x540;
      assert s3.stack[13] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[3] == 0x540;
      assert s4.stack[13] == 0x1b8;
      var s5 := PushN(s4, 1, 0x08);
      assert s5.stack[4] == 0x540;
      assert s5.stack[14] == 0x1b8;
      var s6 := Dup(s5, 1);
      assert s6.stack[5] == 0x540;
      assert s6.stack[15] == 0x1b8;
      var s7 := Dup(s6, 3);
      assert s7.stack[6] == 0x540;
      assert s7.stack[16] == 0x1b8;
      var s8 := MStore(s7);
      assert s8.stack[4] == 0x540;
      assert s8.stack[14] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[5] == 0x540;
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 4);
      assert s10.stack[6] == 0x540;
      assert s10.stack[16] == 0x1b8;
      var s11 := Add(s10);
      assert s11.stack[5] == 0x540;
      assert s11.stack[15] == 0x1b8;
      var s12 := Swap(s11, 1);
      assert s12.stack[5] == 0x540;
      assert s12.stack[15] == 0x1b8;
      var s13 := Swap(s12, 3);
      assert s13.stack[5] == 0x540;
      assert s13.stack[15] == 0x1b8;
      var s14 := MStore(s13);
      assert s14.stack[3] == 0x540;
      assert s14.stack[13] == 0x1b8;
      var s15 := PushN(s14, 1, 0x60);
      assert s15.stack[4] == 0x540;
      assert s15.stack[14] == 0x1b8;
      var s16 := Swap(s15, 2);
      assert s16.stack[4] == 0x540;
      assert s16.stack[14] == 0x1b8;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[5] == 0x540;
      assert s17.stack[15] == 0x1b8;
      var s18 := Dup(s17, 3);
      assert s18.stack[6] == 0x540;
      assert s18.stack[16] == 0x1b8;
      var s19 := Add(s18);
      assert s19.stack[5] == 0x540;
      assert s19.stack[15] == 0x1b8;
      var s20 := Dup(s19, 2);
      assert s20.stack[6] == 0x540;
      assert s20.stack[16] == 0x1b8;
      var s21 := Dup(s20, 1);
      assert s21.stack[7] == 0x540;
      assert s21.stack[17] == 0x1b8;
      var s22 := CallDataSize(s21);
      assert s22.stack[8] == 0x540;
      assert s22.stack[18] == 0x1b8;
      var s23 := Dup(s22, 4);
      assert s23.stack[9] == 0x540;
      assert s23.stack[19] == 0x1b8;
      var s24 := CallDataCopy(s23);
      assert s24.stack[6] == 0x540;
      assert s24.stack[16] == 0x1b8;
      var s25 := Add(s24);
      assert s25.stack[5] == 0x540;
      assert s25.stack[15] == 0x1b8;
      var s26 := Swap(s25, 1);
      assert s26.stack[5] == 0x540;
      assert s26.stack[15] == 0x1b8;
      var s27 := Pop(s26);
      assert s27.stack[4] == 0x540;
      assert s27.stack[14] == 0x1b8;
      var s28 := Pop(s27);
      assert s28.stack[3] == 0x540;
      assert s28.stack[13] == 0x1b8;
      var s29 := Swap(s28, 1);
      assert s29.stack[3] == 0x540;
      assert s29.stack[13] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[2] == 0x540;
      assert s30.stack[12] == 0x1b8;
      var s31 := PushN(s30, 1, 0xc0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s141(s31, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 227
    * Starting at 0x14de
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x540

    requires s0.stack[13] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[4] == 0x540;
      assert s1.stack[14] == 0x1b8;
      var s2 := Swap(s1, 1);
      assert s2.stack[4] == 0x540;
      assert s2.stack[14] == 0x1b8;
      var s3 := Shl(s2);
      assert s3.stack[3] == 0x540;
      assert s3.stack[13] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[4] == 0x540;
      assert s4.stack[14] == 0x1b8;
      var s5 := PushN(s4, 1, 0x07);
      assert s5.stack[5] == 0x540;
      assert s5.stack[15] == 0x1b8;
      var s6 := Byte(s5);
      assert s6.stack[4] == 0x540;
      assert s6.stack[14] == 0x1b8;
      var s7 := PushN(s6, 1, 0xf8);
      assert s7.stack[5] == 0x540;
      assert s7.stack[15] == 0x1b8;
      var s8 := Shl(s7);
      assert s8.stack[4] == 0x540;
      assert s8.stack[14] == 0x1b8;
      var s9 := Dup(s8, 3);
      assert s9.stack[5] == 0x540;
      assert s9.stack[15] == 0x1b8;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[6] == 0x540;
      assert s10.stack[16] == 0x1b8;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x540;
      assert s11.stack[17] == 0x1b8;
      var s12 := MLoad(s11);
      assert s12.stack[7] == 0x540;
      assert s12.stack[17] == 0x1b8;
      var s13 := Dup(s12, 2);
      assert s13.stack[8] == 0x540;
      assert s13.stack[18] == 0x1b8;
      var s14 := Lt(s13);
      assert s14.stack[7] == 0x540;
      assert s14.stack[17] == 0x1b8;
      var s15 := PushN(s14, 2, 0x14f4);
      assert s15.stack[0] == 0x14f4;
      assert s15.stack[8] == 0x540;
      assert s15.stack[18] == 0x1b8;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s16, gas - 1)
      else
        ExecuteFromCFGNode_s142(s16, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 228
    * Starting at 0x14f3
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 143
    * Segment Id for this node is: 229
    * Starting at 0x14f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x540;
      assert s1.stack[16] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x540;
      assert s2.stack[17] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x540;
      assert s3.stack[16] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x540;
      assert s4.stack[15] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x540;
      assert s5.stack[15] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x540;
      assert s6.stack[16] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x540;
      assert s7.stack[16] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x540;
      assert s8.stack[15] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x540;
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x540;
      assert s10.stack[16] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x540;
      assert s11.stack[17] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x540;
      assert s12.stack[16] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x540;
      assert s13.stack[16] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x540;
      assert s14.stack[14] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x540;
      assert s15.stack[13] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x540;
      assert s16.stack[14] == 0x1b8;
      var s17 := PushN(s16, 1, 0x06);
      assert s17.stack[5] == 0x540;
      assert s17.stack[15] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x540;
      assert s18.stack[14] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x540;
      assert s19.stack[15] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x540;
      assert s20.stack[14] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x540;
      assert s21.stack[15] == 0x1b8;
      var s22 := PushN(s21, 1, 0x01);
      assert s22.stack[6] == 0x540;
      assert s22.stack[16] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x540;
      assert s23.stack[17] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x540;
      assert s24.stack[17] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x540;
      assert s25.stack[18] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x540;
      assert s26.stack[17] == 0x1b8;
      var s27 := PushN(s26, 2, 0x1537);
      assert s27.stack[0] == 0x1537;
      assert s27.stack[8] == 0x540;
      assert s27.stack[18] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s28, gas - 1)
      else
        ExecuteFromCFGNode_s144(s28, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 230
    * Starting at 0x1536
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 145
    * Segment Id for this node is: 231
    * Starting at 0x1537
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1537 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x540;
      assert s1.stack[16] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x540;
      assert s2.stack[17] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x540;
      assert s3.stack[16] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x540;
      assert s4.stack[15] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x540;
      assert s5.stack[15] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x540;
      assert s6.stack[16] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x540;
      assert s7.stack[16] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x540;
      assert s8.stack[15] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x540;
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x540;
      assert s10.stack[16] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x540;
      assert s11.stack[17] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x540;
      assert s12.stack[16] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x540;
      assert s13.stack[16] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x540;
      assert s14.stack[14] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x540; 
      assert s15.stack[13] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x540;
      assert s16.stack[14] == 0x1b8;
      var s17 := PushN(s16, 1, 0x05);
      assert s17.stack[5] == 0x540;
      assert s17.stack[15] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x540;
      assert s18.stack[14] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x540;
      assert s19.stack[15] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x540;
      assert s20.stack[14] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x540;
      assert s21.stack[15] == 0x1b8;
      var s22 := PushN(s21, 1, 0x02);
      assert s22.stack[6] == 0x540;
      assert s22.stack[16] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x540;
      assert s23.stack[17] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x540;
      assert s24.stack[17] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x540;
      assert s25.stack[18] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x540;
      assert s26.stack[17] == 0x1b8;
      var s27 := PushN(s26, 2, 0x157a);
      assert s27.stack[0] == 0x157a;
      assert s27.stack[8] == 0x540;
      assert s27.stack[18] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s147(s28, gas - 1)
      else
        ExecuteFromCFGNode_s146(s28, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 232
    * Starting at 0x1579
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1579 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 147
    * Segment Id for this node is: 233
    * Starting at 0x157a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x540;
      assert s1.stack[16] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x540;
      assert s2.stack[17] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x540;
      assert s3.stack[16] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x540;
      assert s4.stack[15] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x540;
      assert s5.stack[15] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x540;
      assert s6.stack[16] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x540;
      assert s7.stack[16] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x540;
      assert s8.stack[15] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x540;
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x540;
      assert s10.stack[16] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x540;
      assert s11.stack[17] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x540;
      assert s12.stack[16] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x540;
      assert s13.stack[16] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x540;
      assert s14.stack[14] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x540;
      assert s15.stack[13] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x540;
      assert s16.stack[14] == 0x1b8;
      var s17 := PushN(s16, 1, 0x04);
      assert s17.stack[5] == 0x540;
      assert s17.stack[15] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x540;
      assert s18.stack[14] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x540;
      assert s19.stack[15] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x540;
      assert s20.stack[14] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x540;
      assert s21.stack[15] == 0x1b8;
      var s22 := PushN(s21, 1, 0x03);
      assert s22.stack[6] == 0x540;
      assert s22.stack[16] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x540;
      assert s23.stack[17] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x540;
      assert s24.stack[17] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x540;
      assert s25.stack[18] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x540;
      assert s26.stack[17] == 0x1b8;
      var s27 := PushN(s26, 2, 0x15bd);
      assert s27.stack[0] == 0x15bd;
      assert s27.stack[8] == 0x540;
      assert s27.stack[18] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s28, gas - 1)
      else
        ExecuteFromCFGNode_s148(s28, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 234
    * Starting at 0x15bc
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 149
    * Segment Id for this node is: 235
    * Starting at 0x15bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x540;
      assert s1.stack[16] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x540;
      assert s2.stack[17] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x540;
      assert s3.stack[16] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x540;
      assert s4.stack[15] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x540;
      assert s5.stack[15] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x540;
      assert s6.stack[16] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x540;
      assert s7.stack[16] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x540;
      assert s8.stack[15] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x540;
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x540;
      assert s10.stack[16] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x540;
      assert s11.stack[17] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x540;
      assert s12.stack[16] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x540;
      assert s13.stack[16] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x540;
      assert s14.stack[14] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x540;
      assert s15.stack[13] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x540;
      assert s16.stack[14] == 0x1b8;
      var s17 := PushN(s16, 1, 0x03);
      assert s17.stack[5] == 0x540;
      assert s17.stack[15] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x540;
      assert s18.stack[14] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x540;
      assert s19.stack[15] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x540;
      assert s20.stack[14] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x540;
      assert s21.stack[15] == 0x1b8;
      var s22 := PushN(s21, 1, 0x04);
      assert s22.stack[6] == 0x540;
      assert s22.stack[16] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x540;
      assert s23.stack[17] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x540;
      assert s24.stack[17] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x540;
      assert s25.stack[18] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x540;
      assert s26.stack[17] == 0x1b8;
      var s27 := PushN(s26, 2, 0x1600);
      assert s27.stack[0] == 0x1600;
      assert s27.stack[8] == 0x540;
      assert s27.stack[18] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s28, gas - 1)
      else
        ExecuteFromCFGNode_s150(s28, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 236
    * Starting at 0x15ff
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 151
    * Segment Id for this node is: 237
    * Starting at 0x1600
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1600 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x540;
      assert s1.stack[16] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x540;
      assert s2.stack[17] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x540;
      assert s3.stack[16] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x540;
      assert s4.stack[15] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x540;
      assert s5.stack[15] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x540;
      assert s6.stack[16] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x540;
      assert s7.stack[16] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x540;
      assert s8.stack[15] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x540;
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x540;
      assert s10.stack[16] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x540;
      assert s11.stack[17] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x540;
      assert s12.stack[16] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x540;
      assert s13.stack[16] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x540;
      assert s14.stack[14] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x540;
      assert s15.stack[13] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x540;
      assert s16.stack[14] == 0x1b8;
      var s17 := PushN(s16, 1, 0x02);
      assert s17.stack[5] == 0x540;
      assert s17.stack[15] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x540;
      assert s18.stack[14] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x540;
      assert s19.stack[15] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x540;
      assert s20.stack[14] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x540;
      assert s21.stack[15] == 0x1b8;
      var s22 := PushN(s21, 1, 0x05);
      assert s22.stack[6] == 0x540;
      assert s22.stack[16] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x540;
      assert s23.stack[17] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x540;
      assert s24.stack[17] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x540;
      assert s25.stack[18] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x540;
      assert s26.stack[17] == 0x1b8;
      var s27 := PushN(s26, 2, 0x1643);
      assert s27.stack[0] == 0x1643;
      assert s27.stack[8] == 0x540;
      assert s27.stack[18] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s153(s28, gas - 1)
      else
        ExecuteFromCFGNode_s152(s28, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 238
    * Starting at 0x1642
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1642 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 153
    * Segment Id for this node is: 239
    * Starting at 0x1643
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1643 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x540;
      assert s1.stack[16] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x540;
      assert s2.stack[17] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x540;
      assert s3.stack[16] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x540;
      assert s4.stack[15] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x540;
      assert s5.stack[15] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x540;
      assert s6.stack[16] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x540;
      assert s7.stack[16] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x540;
      assert s8.stack[15] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x540;
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x540;
      assert s10.stack[16] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x540;
      assert s11.stack[17] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x540;
      assert s12.stack[16] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x540;
      assert s13.stack[16] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x540;
      assert s14.stack[14] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x540;
      assert s15.stack[13] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x540;
      assert s16.stack[14] == 0x1b8;
      var s17 := PushN(s16, 1, 0x01);
      assert s17.stack[5] == 0x540;
      assert s17.stack[15] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x540;
      assert s18.stack[14] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x540;
      assert s19.stack[15] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x540;
      assert s20.stack[14] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x540;
      assert s21.stack[15] == 0x1b8;
      var s22 := PushN(s21, 1, 0x06);
      assert s22.stack[6] == 0x540;
      assert s22.stack[16] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x540;
      assert s23.stack[17] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x540;
      assert s24.stack[17] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x540;
      assert s25.stack[18] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x540;
      assert s26.stack[17] == 0x1b8;
      var s27 := PushN(s26, 2, 0x1686);
      assert s27.stack[0] == 0x1686;
      assert s27.stack[8] == 0x540;
      assert s27.stack[18] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s155(s28, gas - 1)
      else
        ExecuteFromCFGNode_s154(s28, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 240
    * Starting at 0x1685
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1685 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 155
    * Segment Id for this node is: 241
    * Starting at 0x1686
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1686 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x540;
      assert s1.stack[16] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x540;
      assert s2.stack[17] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x540;
      assert s3.stack[16] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x540;
      assert s4.stack[15] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x540;
      assert s5.stack[15] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x540;
      assert s6.stack[16] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x540;
      assert s7.stack[16] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x540;
      assert s8.stack[15] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x540;
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x540;
      assert s10.stack[16] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x540;
      assert s11.stack[17] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x540;
      assert s12.stack[16] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x540;
      assert s13.stack[16] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x540;
      assert s14.stack[14] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x540;
      assert s15.stack[13] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x540;
      assert s16.stack[14] == 0x1b8;
      var s17 := PushN(s16, 1, 0x00);
      assert s17.stack[5] == 0x540;
      assert s17.stack[15] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x540;
      assert s18.stack[14] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x540;
      assert s19.stack[15] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x540;
      assert s20.stack[14] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x540;
      assert s21.stack[15] == 0x1b8;
      var s22 := PushN(s21, 1, 0x07);
      assert s22.stack[6] == 0x540;
      assert s22.stack[16] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x540;
      assert s23.stack[17] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x540;
      assert s24.stack[17] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x540;
      assert s25.stack[18] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x540;
      assert s26.stack[17] == 0x1b8;
      var s27 := PushN(s26, 2, 0x16c9);
      assert s27.stack[0] == 0x16c9;
      assert s27.stack[8] == 0x540;
      assert s27.stack[18] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s157(s28, gas - 1)
      else
        ExecuteFromCFGNode_s156(s28, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 242
    * Starting at 0x16c8
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 157
    * Segment Id for this node is: 243
    * Starting at 0x16c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x540

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x540;
      assert s1.stack[16] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x540;
      assert s2.stack[17] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x540;
      assert s3.stack[16] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x540;
      assert s4.stack[15] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x540;
      assert s5.stack[15] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x540;
      assert s6.stack[16] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x540;
      assert s7.stack[16] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x540;
      assert s8.stack[15] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x540;
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x540;
      assert s10.stack[16] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x540;
      assert s11.stack[17] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x540;
      assert s12.stack[16] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x540;
      assert s13.stack[16] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x540;
      assert s14.stack[14] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x540;
      assert s15.stack[13] == 0x1b8;
      var s16 := Pop(s15);
      assert s16.stack[2] == 0x540;
      assert s16.stack[12] == 0x1b8;
      var s17 := Swap(s16, 2);
      assert s17.stack[0] == 0x540;
      assert s17.stack[12] == 0x1b8;
      var s18 := Swap(s17, 1);
      assert s18.stack[1] == 0x540;
      assert s18.stack[12] == 0x1b8;
      var s19 := Pop(s18);
      assert s19.stack[0] == 0x540;
      assert s19.stack[11] == 0x1b8;
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s20, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 69
    * Starting at 0x540
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x540 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[10] == 0x1b8;
      var s2 := Swap(s1, 1);
      assert s2.stack[10] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[9] == 0x1b8;
      var s4 := PushN(s3, 32, 0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5);
      assert s4.stack[10] == 0x1b8;
      var s5 := Dup(s4, 10);
      assert s5.stack[11] == 0x1b8;
      var s6 := Dup(s5, 10);
      assert s6.stack[12] == 0x1b8;
      var s7 := Dup(s6, 10);
      assert s7.stack[13] == 0x1b8;
      var s8 := Dup(s7, 10);
      assert s8.stack[14] == 0x1b8;
      var s9 := Dup(s8, 6);
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 11);
      assert s10.stack[16] == 0x1b8;
      var s11 := Dup(s10, 11);
      assert s11.stack[17] == 0x1b8;
      var s12 := PushN(s11, 2, 0x0575);
      assert s12.stack[0] == 0x575;
      assert s12.stack[18] == 0x1b8;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[1] == 0x575;
      assert s13.stack[19] == 0x1b8;
      var s14 := SLoad(s13);
      assert s14.stack[1] == 0x575;
      assert s14.stack[19] == 0x1b8;
      var s15 := PushN(s14, 2, 0x14ba);
      assert s15.stack[0] == 0x14ba;
      assert s15.stack[2] == 0x575;
      assert s15.stack[20] == 0x1b8;
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s16, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 226
    * Starting at 0x14ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x575

    requires s0.stack[19] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x575;
      assert s1.stack[19] == 0x1b8;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0x575;
      assert s2.stack[20] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[3] == 0x575;
      assert s3.stack[21] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[3] == 0x575;
      assert s4.stack[21] == 0x1b8;
      var s5 := PushN(s4, 1, 0x08);
      assert s5.stack[4] == 0x575;
      assert s5.stack[22] == 0x1b8;
      var s6 := Dup(s5, 1);
      assert s6.stack[5] == 0x575;
      assert s6.stack[23] == 0x1b8;
      var s7 := Dup(s6, 3);
      assert s7.stack[6] == 0x575;
      assert s7.stack[24] == 0x1b8;
      var s8 := MStore(s7);
      assert s8.stack[4] == 0x575;
      assert s8.stack[22] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[5] == 0x575;
      assert s9.stack[23] == 0x1b8;
      var s10 := Dup(s9, 4);
      assert s10.stack[6] == 0x575;
      assert s10.stack[24] == 0x1b8;
      var s11 := Add(s10);
      assert s11.stack[5] == 0x575;
      assert s11.stack[23] == 0x1b8;
      var s12 := Swap(s11, 1);
      assert s12.stack[5] == 0x575;
      assert s12.stack[23] == 0x1b8;
      var s13 := Swap(s12, 3);
      assert s13.stack[5] == 0x575;
      assert s13.stack[23] == 0x1b8;
      var s14 := MStore(s13);
      assert s14.stack[3] == 0x575;
      assert s14.stack[21] == 0x1b8;
      var s15 := PushN(s14, 1, 0x60);
      assert s15.stack[4] == 0x575;
      assert s15.stack[22] == 0x1b8;
      var s16 := Swap(s15, 2);
      assert s16.stack[4] == 0x575;
      assert s16.stack[22] == 0x1b8;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[5] == 0x575;
      assert s17.stack[23] == 0x1b8;
      var s18 := Dup(s17, 3);
      assert s18.stack[6] == 0x575;
      assert s18.stack[24] == 0x1b8;
      var s19 := Add(s18);
      assert s19.stack[5] == 0x575;
      assert s19.stack[23] == 0x1b8;
      var s20 := Dup(s19, 2);
      assert s20.stack[6] == 0x575;
      assert s20.stack[24] == 0x1b8;
      var s21 := Dup(s20, 1);
      assert s21.stack[7] == 0x575;
      assert s21.stack[25] == 0x1b8;
      var s22 := CallDataSize(s21);
      assert s22.stack[8] == 0x575;
      assert s22.stack[26] == 0x1b8;
      var s23 := Dup(s22, 4);
      assert s23.stack[9] == 0x575;
      assert s23.stack[27] == 0x1b8;
      var s24 := CallDataCopy(s23);
      assert s24.stack[6] == 0x575;
      assert s24.stack[24] == 0x1b8;
      var s25 := Add(s24);
      assert s25.stack[5] == 0x575;
      assert s25.stack[23] == 0x1b8;
      var s26 := Swap(s25, 1);
      assert s26.stack[5] == 0x575;
      assert s26.stack[23] == 0x1b8;
      var s27 := Pop(s26);
      assert s27.stack[4] == 0x575;
      assert s27.stack[22] == 0x1b8;
      var s28 := Pop(s27);
      assert s28.stack[3] == 0x575;
      assert s28.stack[21] == 0x1b8;
      var s29 := Swap(s28, 1);
      assert s29.stack[3] == 0x575;
      assert s29.stack[21] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[2] == 0x575;
      assert s30.stack[20] == 0x1b8;
      var s31 := PushN(s30, 1, 0xc0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s160(s31, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 227
    * Starting at 0x14de
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x575

    requires s0.stack[21] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[4] == 0x575;
      assert s1.stack[22] == 0x1b8;
      var s2 := Swap(s1, 1);
      assert s2.stack[4] == 0x575;
      assert s2.stack[22] == 0x1b8;
      var s3 := Shl(s2);
      assert s3.stack[3] == 0x575;
      assert s3.stack[21] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[4] == 0x575;
      assert s4.stack[22] == 0x1b8;
      var s5 := PushN(s4, 1, 0x07);
      assert s5.stack[5] == 0x575;
      assert s5.stack[23] == 0x1b8;
      var s6 := Byte(s5);
      assert s6.stack[4] == 0x575;
      assert s6.stack[22] == 0x1b8;
      var s7 := PushN(s6, 1, 0xf8);
      assert s7.stack[5] == 0x575;
      assert s7.stack[23] == 0x1b8;
      var s8 := Shl(s7);
      assert s8.stack[4] == 0x575;
      assert s8.stack[22] == 0x1b8;
      var s9 := Dup(s8, 3);
      assert s9.stack[5] == 0x575;
      assert s9.stack[23] == 0x1b8;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[6] == 0x575;
      assert s10.stack[24] == 0x1b8;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x575;
      assert s11.stack[25] == 0x1b8;
      var s12 := MLoad(s11);
      assert s12.stack[7] == 0x575;
      assert s12.stack[25] == 0x1b8;
      var s13 := Dup(s12, 2);
      assert s13.stack[8] == 0x575;
      assert s13.stack[26] == 0x1b8;
      var s14 := Lt(s13);
      assert s14.stack[7] == 0x575;
      assert s14.stack[25] == 0x1b8;
      var s15 := PushN(s14, 2, 0x14f4);
      assert s15.stack[0] == 0x14f4;
      assert s15.stack[8] == 0x575;
      assert s15.stack[26] == 0x1b8;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s162(s16, gas - 1)
      else
        ExecuteFromCFGNode_s161(s16, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 228
    * Starting at 0x14f3
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 162
    * Segment Id for this node is: 229
    * Starting at 0x14f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x575;
      assert s1.stack[24] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x575;
      assert s2.stack[25] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x575;
      assert s3.stack[24] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x575;
      assert s4.stack[23] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x575;
      assert s5.stack[23] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x575;
      assert s6.stack[24] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x575;
      assert s7.stack[24] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x575;
      assert s8.stack[23] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x575;
      assert s9.stack[23] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x575;
      assert s10.stack[24] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x575;
      assert s11.stack[25] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x575;
      assert s12.stack[24] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x575;
      assert s13.stack[24] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x575;
      assert s14.stack[22] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x575;
      assert s15.stack[21] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x575;
      assert s16.stack[22] == 0x1b8;
      var s17 := PushN(s16, 1, 0x06);
      assert s17.stack[5] == 0x575;
      assert s17.stack[23] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x575;
      assert s18.stack[22] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x575;
      assert s19.stack[23] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x575;
      assert s20.stack[22] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x575;
      assert s21.stack[23] == 0x1b8;
      var s22 := PushN(s21, 1, 0x01);
      assert s22.stack[6] == 0x575;
      assert s22.stack[24] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x575;
      assert s23.stack[25] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x575;
      assert s24.stack[25] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x575;
      assert s25.stack[26] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x575;
      assert s26.stack[25] == 0x1b8;
      var s27 := PushN(s26, 2, 0x1537);
      assert s27.stack[0] == 0x1537;
      assert s27.stack[8] == 0x575;
      assert s27.stack[26] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s28, gas - 1)
      else
        ExecuteFromCFGNode_s163(s28, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 230
    * Starting at 0x1536
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 164
    * Segment Id for this node is: 231
    * Starting at 0x1537
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1537 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x575;
      assert s1.stack[24] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x575;
      assert s2.stack[25] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x575;
      assert s3.stack[24] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x575;
      assert s4.stack[23] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x575;
      assert s5.stack[23] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x575;
      assert s6.stack[24] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x575;
      assert s7.stack[24] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x575;
      assert s8.stack[23] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x575;
      assert s9.stack[23] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x575;
      assert s10.stack[24] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x575;
      assert s11.stack[25] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x575;
      assert s12.stack[24] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x575;
      assert s13.stack[24] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x575;
      assert s14.stack[22] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x575;
      assert s15.stack[21] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x575;
      assert s16.stack[22] == 0x1b8;
      var s17 := PushN(s16, 1, 0x05);
      assert s17.stack[5] == 0x575;
      assert s17.stack[23] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x575;
      assert s18.stack[22] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x575;
      assert s19.stack[23] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x575;
      assert s20.stack[22] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x575;
      assert s21.stack[23] == 0x1b8;
      var s22 := PushN(s21, 1, 0x02);
      assert s22.stack[6] == 0x575;
      assert s22.stack[24] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x575;
      assert s23.stack[25] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x575;
      assert s24.stack[25] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x575;
      assert s25.stack[26] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x575;
      assert s26.stack[25] == 0x1b8;
      var s27 := PushN(s26, 2, 0x157a);
      assert s27.stack[0] == 0x157a;
      assert s27.stack[8] == 0x575;
      assert s27.stack[26] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s166(s28, gas - 1)
      else
        ExecuteFromCFGNode_s165(s28, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 232
    * Starting at 0x1579
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1579 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 166
    * Segment Id for this node is: 233
    * Starting at 0x157a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x575;
      assert s1.stack[24] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x575;
      assert s2.stack[25] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x575;
      assert s3.stack[24] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x575;
      assert s4.stack[23] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x575;
      assert s5.stack[23] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x575;
      assert s6.stack[24] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x575;
      assert s7.stack[24] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x575;
      assert s8.stack[23] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x575;
      assert s9.stack[23] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x575;
      assert s10.stack[24] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x575;
      assert s11.stack[25] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x575;
      assert s12.stack[24] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x575;
      assert s13.stack[24] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x575;
      assert s14.stack[22] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x575;
      assert s15.stack[21] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x575;
      assert s16.stack[22] == 0x1b8;
      var s17 := PushN(s16, 1, 0x04);
      assert s17.stack[5] == 0x575;
      assert s17.stack[23] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x575;
      assert s18.stack[22] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x575;
      assert s19.stack[23] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x575;
      assert s20.stack[22] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x575;
      assert s21.stack[23] == 0x1b8;
      var s22 := PushN(s21, 1, 0x03);
      assert s22.stack[6] == 0x575;
      assert s22.stack[24] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x575;
      assert s23.stack[25] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x575;
      assert s24.stack[25] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x575;
      assert s25.stack[26] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x575;
      assert s26.stack[25] == 0x1b8;
      var s27 := PushN(s26, 2, 0x15bd);
      assert s27.stack[0] == 0x15bd;
      assert s27.stack[8] == 0x575;
      assert s27.stack[26] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s168(s28, gas - 1)
      else
        ExecuteFromCFGNode_s167(s28, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 234
    * Starting at 0x15bc
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 168
    * Segment Id for this node is: 235
    * Starting at 0x15bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x575;
      assert s1.stack[24] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x575;
      assert s2.stack[25] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x575;
      assert s3.stack[24] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x575;
      assert s4.stack[23] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x575;
      assert s5.stack[23] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x575;
      assert s6.stack[24] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x575;
      assert s7.stack[24] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x575;
      assert s8.stack[23] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x575;
      assert s9.stack[23] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x575;
      assert s10.stack[24] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x575;
      assert s11.stack[25] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x575;
      assert s12.stack[24] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x575;
      assert s13.stack[24] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x575;
      assert s14.stack[22] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x575;
      assert s15.stack[21] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x575;
      assert s16.stack[22] == 0x1b8;
      var s17 := PushN(s16, 1, 0x03);
      assert s17.stack[5] == 0x575;
      assert s17.stack[23] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x575;
      assert s18.stack[22] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x575;
      assert s19.stack[23] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x575;
      assert s20.stack[22] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x575;
      assert s21.stack[23] == 0x1b8;
      var s22 := PushN(s21, 1, 0x04);
      assert s22.stack[6] == 0x575;
      assert s22.stack[24] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x575;
      assert s23.stack[25] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x575;
      assert s24.stack[25] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x575;
      assert s25.stack[26] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x575;
      assert s26.stack[25] == 0x1b8;
      var s27 := PushN(s26, 2, 0x1600);
      assert s27.stack[0] == 0x1600;
      assert s27.stack[8] == 0x575;
      assert s27.stack[26] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s28, gas - 1)
      else
        ExecuteFromCFGNode_s169(s28, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 236
    * Starting at 0x15ff
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 170
    * Segment Id for this node is: 237
    * Starting at 0x1600
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1600 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x575;
      assert s1.stack[24] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x575;
      assert s2.stack[25] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x575;
      assert s3.stack[24] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x575;
      assert s4.stack[23] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x575;
      assert s5.stack[23] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x575;
      assert s6.stack[24] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x575;
      assert s7.stack[24] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x575;
      assert s8.stack[23] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x575;
      assert s9.stack[23] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x575;
      assert s10.stack[24] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x575;
      assert s11.stack[25] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x575;
      assert s12.stack[24] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x575;
      assert s13.stack[24] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x575;
      assert s14.stack[22] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x575;
      assert s15.stack[21] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x575;
      assert s16.stack[22] == 0x1b8;
      var s17 := PushN(s16, 1, 0x02);
      assert s17.stack[5] == 0x575;
      assert s17.stack[23] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x575;
      assert s18.stack[22] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x575;
      assert s19.stack[23] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x575;
      assert s20.stack[22] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x575;
      assert s21.stack[23] == 0x1b8;
      var s22 := PushN(s21, 1, 0x05);
      assert s22.stack[6] == 0x575;
      assert s22.stack[24] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x575;
      assert s23.stack[25] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x575;
      assert s24.stack[25] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x575;
      assert s25.stack[26] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x575;
      assert s26.stack[25] == 0x1b8;
      var s27 := PushN(s26, 2, 0x1643);
      assert s27.stack[0] == 0x1643;
      assert s27.stack[8] == 0x575;
      assert s27.stack[26] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s28, gas - 1)
      else
        ExecuteFromCFGNode_s171(s28, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 238
    * Starting at 0x1642
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1642 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 172
    * Segment Id for this node is: 239
    * Starting at 0x1643
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1643 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x575;
      assert s1.stack[24] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x575;
      assert s2.stack[25] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x575;
      assert s3.stack[24] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x575;
      assert s4.stack[23] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x575;
      assert s5.stack[23] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x575;
      assert s6.stack[24] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x575;
      assert s7.stack[24] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x575;
      assert s8.stack[23] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x575;
      assert s9.stack[23] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x575;
      assert s10.stack[24] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x575;
      assert s11.stack[25] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x575;
      assert s12.stack[24] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x575;
      assert s13.stack[24] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x575;
      assert s14.stack[22] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x575;
      assert s15.stack[21] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x575;
      assert s16.stack[22] == 0x1b8;
      var s17 := PushN(s16, 1, 0x01);
      assert s17.stack[5] == 0x575;
      assert s17.stack[23] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x575;
      assert s18.stack[22] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x575;
      assert s19.stack[23] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x575;
      assert s20.stack[22] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x575;
      assert s21.stack[23] == 0x1b8;
      var s22 := PushN(s21, 1, 0x06);
      assert s22.stack[6] == 0x575;
      assert s22.stack[24] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x575;
      assert s23.stack[25] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x575;
      assert s24.stack[25] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x575;
      assert s25.stack[26] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x575;
      assert s26.stack[25] == 0x1b8;
      var s27 := PushN(s26, 2, 0x1686);
      assert s27.stack[0] == 0x1686;
      assert s27.stack[8] == 0x575;
      assert s27.stack[26] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s28, gas - 1)
      else
        ExecuteFromCFGNode_s173(s28, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 240
    * Starting at 0x1685
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1685 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 174
    * Segment Id for this node is: 241
    * Starting at 0x1686
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1686 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x575;
      assert s1.stack[24] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x575;
      assert s2.stack[25] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x575;
      assert s3.stack[24] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x575;
      assert s4.stack[23] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x575;
      assert s5.stack[23] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x575;
      assert s6.stack[24] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x575;
      assert s7.stack[24] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x575;
      assert s8.stack[23] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x575;
      assert s9.stack[23] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x575;
      assert s10.stack[24] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x575;
      assert s11.stack[25] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x575;
      assert s12.stack[24] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x575;
      assert s13.stack[24] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x575;
      assert s14.stack[22] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x575;
      assert s15.stack[21] == 0x1b8;
      var s16 := Dup(s15, 1);
      assert s16.stack[4] == 0x575;
      assert s16.stack[22] == 0x1b8;
      var s17 := PushN(s16, 1, 0x00);
      assert s17.stack[5] == 0x575;
      assert s17.stack[23] == 0x1b8;
      var s18 := Byte(s17);
      assert s18.stack[4] == 0x575;
      assert s18.stack[22] == 0x1b8;
      var s19 := PushN(s18, 1, 0xf8);
      assert s19.stack[5] == 0x575;
      assert s19.stack[23] == 0x1b8;
      var s20 := Shl(s19);
      assert s20.stack[4] == 0x575;
      assert s20.stack[22] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[5] == 0x575;
      assert s21.stack[23] == 0x1b8;
      var s22 := PushN(s21, 1, 0x07);
      assert s22.stack[6] == 0x575;
      assert s22.stack[24] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x575;
      assert s23.stack[25] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[7] == 0x575;
      assert s24.stack[25] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[8] == 0x575;
      assert s25.stack[26] == 0x1b8;
      var s26 := Lt(s25);
      assert s26.stack[7] == 0x575;
      assert s26.stack[25] == 0x1b8;
      var s27 := PushN(s26, 2, 0x16c9);
      assert s27.stack[0] == 0x16c9;
      assert s27.stack[8] == 0x575;
      assert s27.stack[26] == 0x1b8;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s28, gas - 1)
      else
        ExecuteFromCFGNode_s175(s28, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 242
    * Starting at 0x16c8
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 176
    * Segment Id for this node is: 243
    * Starting at 0x16c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x575

    requires s0.stack[24] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x575;
      assert s1.stack[24] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x575;
      assert s2.stack[25] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x575;
      assert s3.stack[24] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[5] == 0x575;
      assert s4.stack[23] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[5] == 0x575;
      assert s5.stack[23] == 0x1b8;
      var s6 := PushN(s5, 31, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x575;
      assert s6.stack[24] == 0x1b8;
      var s7 := Not(s6);
      assert s7.stack[6] == 0x575;
      assert s7.stack[24] == 0x1b8;
      var s8 := And(s7);
      assert s8.stack[5] == 0x575;
      assert s8.stack[23] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[5] == 0x575;
      assert s9.stack[23] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x575;
      assert s10.stack[24] == 0x1b8;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[7] == 0x575;
      assert s11.stack[25] == 0x1b8;
      var s12 := Byte(s11);
      assert s12.stack[6] == 0x575;
      assert s12.stack[24] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[6] == 0x575;
      assert s13.stack[24] == 0x1b8;
      var s14 := MStore8(s13);
      assert s14.stack[4] == 0x575;
      assert s14.stack[22] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[3] == 0x575;
      assert s15.stack[21] == 0x1b8;
      var s16 := Pop(s15);
      assert s16.stack[2] == 0x575;
      assert s16.stack[20] == 0x1b8;
      var s17 := Swap(s16, 2);
      assert s17.stack[0] == 0x575;
      assert s17.stack[20] == 0x1b8;
      var s18 := Swap(s17, 1);
      assert s18.stack[1] == 0x575;
      assert s18.stack[20] == 0x1b8;
      var s19 := Pop(s18);
      assert s19.stack[0] == 0x575;
      assert s19.stack[19] == 0x1b8;
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s20, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 70
    * Starting at 0x575
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x575 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[18] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[18] == 0x1b8;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[19] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[20] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[20] == 0x1b8;
      var s5 := PushN(s4, 1, 0xa0);
      assert s5.stack[21] == 0x1b8;
      var s6 := Dup(s5, 1);
      assert s6.stack[22] == 0x1b8;
      var s7 := Dup(s6, 3);
      assert s7.stack[23] == 0x1b8;
      var s8 := MStore(s7);
      assert s8.stack[21] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[22] == 0x1b8;
      var s10 := Add(s9);
      assert s10.stack[21] == 0x1b8;
      var s11 := Dup(s10, 10);
      assert s11.stack[22] == 0x1b8;
      var s12 := Swap(s11, 1);
      assert s12.stack[22] == 0x1b8;
      var s13 := MStore(s12);
      assert s13.stack[20] == 0x1b8;
      var s14 := Swap(s13, 1);
      assert s14.stack[20] == 0x1b8;
      var s15 := Dup(s14, 2);
      assert s15.stack[21] == 0x1b8;
      var s16 := Swap(s15, 1);
      assert s16.stack[21] == 0x1b8;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[22] == 0x1b8;
      var s18 := Dup(s17, 3);
      assert s18.stack[23] == 0x1b8;
      var s19 := Add(s18);
      assert s19.stack[22] == 0x1b8;
      var s20 := Swap(s19, 1);
      assert s20.stack[22] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[23] == 0x1b8;
      var s22 := Add(s21);
      assert s22.stack[22] == 0x1b8;
      var s23 := PushN(s22, 1, 0x60);
      assert s23.stack[23] == 0x1b8;
      var s24 := Dup(s23, 4);
      assert s24.stack[24] == 0x1b8;
      var s25 := Add(s24);
      assert s25.stack[23] == 0x1b8;
      var s26 := PushN(s25, 1, 0x80);
      assert s26.stack[24] == 0x1b8;
      var s27 := Dup(s26, 5);
      assert s27.stack[25] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[24] == 0x1b8;
      var s29 := PushN(s28, 1, 0xc0);
      assert s29.stack[25] == 0x1b8;
      var s30 := Dup(s29, 6);
      assert s30.stack[26] == 0x1b8;
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s178(s31, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 71
    * Starting at 0x59a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 15
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[25] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 15);
      assert s1.stack[26] == 0x1b8;
      var s2 := Dup(s1, 15);
      assert s2.stack[27] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[28] == 0x1b8;
      var s4 := Dup(s3, 3);
      assert s4.stack[29] == 0x1b8;
      var s5 := Dup(s4, 5);
      assert s5.stack[30] == 0x1b8;
      var s6 := CallDataCopy(s5);
      assert s6.stack[27] == 0x1b8;
      var s7 := PushN(s6, 1, 0x00);
      assert s7.stack[28] == 0x1b8;
      var s8 := Dup(s7, 4);
      assert s8.stack[29] == 0x1b8;
      var s9 := Dup(s8, 3);
      assert s9.stack[30] == 0x1b8;
      var s10 := Add(s9);
      assert s10.stack[29] == 0x1b8;
      var s11 := MStore(s10);
      assert s11.stack[27] == 0x1b8;
      var s12 := PushN(s11, 1, 0x1f);
      assert s12.stack[28] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[27] == 0x1b8;
      var s14 := PushN(s13, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s14.stack[28] == 0x1b8;
      var s15 := And(s14);
      assert s15.stack[27] == 0x1b8;
      var s16 := Swap(s15, 1);
      assert s16.stack[27] == 0x1b8;
      var s17 := Swap(s16, 2);
      assert s17.stack[27] == 0x1b8;
      var s18 := Add(s17);
      assert s18.stack[26] == 0x1b8;
      var s19 := Dup(s18, 8);
      assert s19.stack[27] == 0x1b8;
      var s20 := Dup(s19, 2);
      assert s20.stack[28] == 0x1b8;
      var s21 := Sub(s20);
      assert s21.stack[27] == 0x1b8;
      var s22 := Dup(s21, 7);
      assert s22.stack[28] == 0x1b8;
      var s23 := MStore(s22);
      assert s23.stack[26] == 0x1b8;
      var s24 := Dup(s23, 13);
      assert s24.stack[27] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[28] == 0x1b8;
      var s26 := MStore(s25);
      assert s26.stack[26] == 0x1b8;
      var s27 := PushN(s26, 1, 0x20);
      assert s27.stack[27] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[26] == 0x1b8;
      var s29 := Swap(s28, 1);
      assert s29.stack[26] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[25] == 0x1b8;
      var s31 := Dup(s30, 13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s179(s31, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 72
    * Starting at 0x5dc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[26] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 13);
      assert s1.stack[27] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[28] == 0x1b8;
      var s3 := Dup(s2, 3);
      assert s3.stack[29] == 0x1b8;
      var s4 := Dup(s3, 5);
      assert s4.stack[30] == 0x1b8;
      var s5 := CallDataCopy(s4);
      assert s5.stack[27] == 0x1b8;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[28] == 0x1b8;
      var s7 := Dup(s6, 4);
      assert s7.stack[29] == 0x1b8;
      var s8 := Dup(s7, 3);
      assert s8.stack[30] == 0x1b8;
      var s9 := Add(s8);
      assert s9.stack[29] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[30] == 0x1b8;
      var s11 := Swap(s10, 1);
      assert s11.stack[30] == 0x1b8;
      var s12 := MStore(s11);
      assert s12.stack[28] == 0x1b8;
      var s13 := PushN(s12, 1, 0x1f);
      assert s13.stack[29] == 0x1b8;
      var s14 := Swap(s13, 1);
      assert s14.stack[29] == 0x1b8;
      var s15 := Swap(s14, 2);
      assert s15.stack[29] == 0x1b8;
      var s16 := Add(s15);
      assert s16.stack[28] == 0x1b8;
      var s17 := PushN(s16, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s17.stack[29] == 0x1b8;
      var s18 := And(s17);
      assert s18.stack[28] == 0x1b8;
      var s19 := Swap(s18, 1);
      assert s19.stack[28] == 0x1b8;
      var s20 := Swap(s19, 3);
      assert s20.stack[28] == 0x1b8;
      var s21 := Add(s20);
      assert s21.stack[27] == 0x1b8;
      var s22 := Dup(s21, 9);
      assert s22.stack[28] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[29] == 0x1b8;
      var s24 := Sub(s23);
      assert s24.stack[28] == 0x1b8;
      var s25 := Dup(s24, 7);
      assert s25.stack[29] == 0x1b8;
      var s26 := MStore(s25);
      assert s26.stack[27] == 0x1b8;
      var s27 := Dup(s26, 13);
      assert s27.stack[28] == 0x1b8;
      var s28 := MLoad(s27);
      assert s28.stack[28] == 0x1b8;
      var s29 := Dup(s28, 2);
      assert s29.stack[29] == 0x1b8;
      var s30 := MStore(s29);
      assert s30.stack[27] == 0x1b8;
      var s31 := Dup(s30, 13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s180(s31, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 73
    * Starting at 0x61d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[28] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MLoad(s0);
      assert s1.stack[28] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[29] == 0x1b8;
      var s3 := Swap(s2, 2);
      assert s3.stack[29] == 0x1b8;
      var s4 := Dup(s3, 3);
      assert s4.stack[30] == 0x1b8;
      var s5 := Add(s4);
      assert s5.stack[29] == 0x1b8;
      var s6 := Swap(s5, 4);
      assert s6.stack[29] == 0x1b8;
      var s7 := Swap(s6, 2);
      assert s7.stack[29] == 0x1b8;
      var s8 := Dup(s7, 15);
      assert s8.stack[30] == 0x1b8;
      var s9 := Add(s8);
      assert s9.stack[29] == 0x1b8;
      var s10 := Swap(s9, 3);
      assert s10.stack[29] == 0x1b8;
      var s11 := Pop(s10);
      assert s11.stack[28] == 0x1b8;
      var s12 := Swap(s11, 1);
      assert s12.stack[28] == 0x1b8;
      var s13 := Dup(s12, 2);
      assert s13.stack[29] == 0x1b8;
      var s14 := Swap(s13, 1);
      assert s14.stack[29] == 0x1b8;
      var s15 := Dup(s14, 5);
      assert s15.stack[30] == 0x1b8;
      var s16 := Swap(s15, 1);
      assert s16.stack[30] == 0x1b8;
      var s17 := Dup(s16, 5);
      assert s17.stack[31] == 0x1b8;
      var s18 := Swap(s17, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s181(s18, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 74
    * Starting at 0x630
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x630 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[31] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[31] == 0x1b8;
      var s2 := Dup(s1, 4);
      assert s2.stack[32] == 0x1b8;
      var s3 := Dup(s2, 2);
      assert s3.stack[33] == 0x1b8;
      var s4 := Lt(s3);
      assert s4.stack[32] == 0x1b8;
      var s5 := IsZero(s4);
      assert s5.stack[32] == 0x1b8;
      var s6 := PushN(s5, 2, 0x0648);
      assert s6.stack[0] == 0x648;
      assert s6.stack[33] == 0x1b8;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s7, gas - 1)
      else
        ExecuteFromCFGNode_s182(s7, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 75
    * Starting at 0x639
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x639 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[31] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[32] == 0x1b8;
      var s2 := Dup(s1, 2);
      assert s2.stack[33] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[32] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[32] == 0x1b8;
      var s5 := Dup(s4, 4);
      assert s5.stack[33] == 0x1b8;
      var s6 := Dup(s5, 3);
      assert s6.stack[34] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[33] == 0x1b8;
      var s8 := MStore(s7);
      assert s8.stack[31] == 0x1b8;
      var s9 := PushN(s8, 1, 0x20);
      assert s9.stack[32] == 0x1b8;
      var s10 := Add(s9);
      assert s10.stack[31] == 0x1b8;
      var s11 := PushN(s10, 2, 0x0630);
      assert s11.stack[0] == 0x630;
      assert s11.stack[32] == 0x1b8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s12, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 76
    * Starting at 0x648
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x648 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[31] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[31] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[30] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[29] == 0x1b8;
      var s4 := Pop(s3);
      assert s4.stack[28] == 0x1b8;
      var s5 := Pop(s4);
      assert s5.stack[27] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[27] == 0x1b8;
      var s7 := Pop(s6);
      assert s7.stack[26] == 0x1b8;
      var s8 := Swap(s7, 1);
      assert s8.stack[26] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[27] == 0x1b8;
      var s10 := Add(s9);
      assert s10.stack[26] == 0x1b8;
      var s11 := Swap(s10, 1);
      assert s11.stack[26] == 0x1b8;
      var s12 := PushN(s11, 1, 0x1f);
      assert s12.stack[27] == 0x1b8;
      var s13 := And(s12);
      assert s13.stack[26] == 0x1b8;
      var s14 := Dup(s13, 1);
      assert s14.stack[27] == 0x1b8;
      var s15 := IsZero(s14);
      assert s15.stack[27] == 0x1b8;
      var s16 := PushN(s15, 2, 0x0675);
      assert s16.stack[0] == 0x675;
      assert s16.stack[28] == 0x1b8;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s185(s17, gas - 1)
      else
        ExecuteFromCFGNode_s184(s17, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 77
    * Starting at 0x65c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[26] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[27] == 0x1b8;
      var s2 := Dup(s1, 3);
      assert s2.stack[28] == 0x1b8;
      var s3 := Sub(s2);
      assert s3.stack[27] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[28] == 0x1b8;
      var s5 := MLoad(s4);
      assert s5.stack[28] == 0x1b8;
      var s6 := PushN(s5, 1, 0x01);
      assert s6.stack[29] == 0x1b8;
      var s7 := Dup(s6, 4);
      assert s7.stack[30] == 0x1b8;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[31] == 0x1b8;
      var s9 := Sub(s8);
      assert s9.stack[30] == 0x1b8;
      var s10 := PushN(s9, 2, 0x0100);
      assert s10.stack[31] == 0x1b8;
      var s11 := Exp(s10);
      assert s11.stack[30] == 0x1b8;
      var s12 := Sub(s11);
      assert s12.stack[29] == 0x1b8;
      var s13 := Not(s12);
      assert s13.stack[29] == 0x1b8;
      var s14 := And(s13);
      assert s14.stack[28] == 0x1b8;
      var s15 := Dup(s14, 2);
      assert s15.stack[29] == 0x1b8;
      var s16 := MStore(s15);
      assert s16.stack[27] == 0x1b8;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[28] == 0x1b8;
      var s18 := Add(s17);
      assert s18.stack[27] == 0x1b8;
      var s19 := Swap(s18, 2);
      assert s19.stack[27] == 0x1b8;
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s185(s20, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 78
    * Starting at 0x675
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x675 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[26] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[26] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[25] == 0x1b8;
      var s3 := Dup(s2, 7);
      assert s3.stack[26] == 0x1b8;
      var s4 := Dup(s3, 2);
      assert s4.stack[27] == 0x1b8;
      var s5 := Sub(s4);
      assert s5.stack[26] == 0x1b8;
      var s6 := Dup(s5, 4);
      assert s6.stack[27] == 0x1b8;
      var s7 := MStore(s6);
      assert s7.stack[25] == 0x1b8;
      var s8 := Dup(s7, 9);
      assert s8.stack[26] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[27] == 0x1b8;
      var s10 := MStore(s9);
      assert s10.stack[25] == 0x1b8;
      var s11 := PushN(s10, 1, 0x20);
      assert s11.stack[26] == 0x1b8;
      var s12 := Add(s11);
      assert s12.stack[25] == 0x1b8;
      var s13 := Dup(s12, 10);
      assert s13.stack[26] == 0x1b8;
      var s14 := Dup(s13, 10);
      assert s14.stack[27] == 0x1b8;
      var s15 := Dup(s14, 1);
      assert s15.stack[28] == 0x1b8;
      var s16 := Dup(s15, 3);
      assert s16.stack[29] == 0x1b8;
      var s17 := Dup(s16, 5);
      assert s17.stack[30] == 0x1b8;
      var s18 := CallDataCopy(s17);
      assert s18.stack[27] == 0x1b8;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[28] == 0x1b8;
      var s20 := Dup(s19, 4);
      assert s20.stack[29] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[30] == 0x1b8;
      var s22 := Add(s21);
      assert s22.stack[29] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[30] == 0x1b8;
      var s24 := Swap(s23, 1);
      assert s24.stack[30] == 0x1b8;
      var s25 := MStore(s24);
      assert s25.stack[28] == 0x1b8;
      var s26 := PushN(s25, 1, 0x1f);
      assert s26.stack[29] == 0x1b8;
      var s27 := Swap(s26, 1);
      assert s27.stack[29] == 0x1b8;
      var s28 := Swap(s27, 2);
      assert s28.stack[29] == 0x1b8;
      var s29 := Add(s28);
      assert s29.stack[28] == 0x1b8;
      var s30 := PushN(s29, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s30.stack[29] == 0x1b8;
      var s31 := And(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s186(s31, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 79
    * Starting at 0x6b7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[28] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[28] == 0x1b8;
      var s2 := Swap(s1, 3);
      assert s2.stack[28] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[27] == 0x1b8;
      var s4 := Dup(s3, 9);
      assert s4.stack[28] == 0x1b8;
      var s5 := Dup(s4, 2);
      assert s5.stack[29] == 0x1b8;
      var s6 := Sub(s5);
      assert s6.stack[28] == 0x1b8;
      var s7 := Dup(s6, 5);
      assert s7.stack[29] == 0x1b8;
      var s8 := MStore(s7);
      assert s8.stack[27] == 0x1b8;
      var s9 := Dup(s8, 10);
      assert s9.stack[28] == 0x1b8;
      var s10 := MLoad(s9);
      assert s10.stack[28] == 0x1b8;
      var s11 := Dup(s10, 2);
      assert s11.stack[29] == 0x1b8;
      var s12 := MStore(s11);
      assert s12.stack[27] == 0x1b8;
      var s13 := Dup(s12, 10);
      assert s13.stack[28] == 0x1b8;
      var s14 := MLoad(s13);
      assert s14.stack[28] == 0x1b8;
      var s15 := PushN(s14, 1, 0x20);
      assert s15.stack[29] == 0x1b8;
      var s16 := Swap(s15, 2);
      assert s16.stack[29] == 0x1b8;
      var s17 := Dup(s16, 3);
      assert s17.stack[30] == 0x1b8;
      var s18 := Add(s17);
      assert s18.stack[29] == 0x1b8;
      var s19 := Swap(s18, 4);
      assert s19.stack[29] == 0x1b8;
      var s20 := Swap(s19, 2);
      assert s20.stack[29] == 0x1b8;
      var s21 := Dup(s20, 12);
      assert s21.stack[30] == 0x1b8;
      var s22 := Add(s21);
      assert s22.stack[29] == 0x1b8;
      var s23 := Swap(s22, 3);
      assert s23.stack[29] == 0x1b8;
      var s24 := Pop(s23);
      assert s24.stack[28] == 0x1b8;
      var s25 := Swap(s24, 1);
      assert s25.stack[28] == 0x1b8;
      var s26 := Dup(s25, 2);
      assert s26.stack[29] == 0x1b8;
      var s27 := Swap(s26, 1);
      assert s27.stack[29] == 0x1b8;
      var s28 := Dup(s27, 5);
      assert s28.stack[30] == 0x1b8;
      var s29 := Swap(s28, 1);
      assert s29.stack[30] == 0x1b8;
      var s30 := Dup(s29, 5);
      assert s30.stack[31] == 0x1b8;
      var s31 := Swap(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s187(s31, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 80
    * Starting at 0x6d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[31] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[31] == 0x1b8;
      var s2 := Dup(s1, 4);
      assert s2.stack[32] == 0x1b8;
      var s3 := Dup(s2, 2);
      assert s3.stack[33] == 0x1b8;
      var s4 := Lt(s3);
      assert s4.stack[32] == 0x1b8;
      var s5 := IsZero(s4);
      assert s5.stack[32] == 0x1b8;
      var s6 := PushN(s5, 2, 0x06ef);
      assert s6.stack[0] == 0x6ef;
      assert s6.stack[33] == 0x1b8;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s7, gas - 1)
      else
        ExecuteFromCFGNode_s188(s7, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 81
    * Starting at 0x6e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[31] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[32] == 0x1b8;
      var s2 := Dup(s1, 2);
      assert s2.stack[33] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[32] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[32] == 0x1b8;
      var s5 := Dup(s4, 4);
      assert s5.stack[33] == 0x1b8;
      var s6 := Dup(s5, 3);
      assert s6.stack[34] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[33] == 0x1b8;
      var s8 := MStore(s7);
      assert s8.stack[31] == 0x1b8;
      var s9 := PushN(s8, 1, 0x20);
      assert s9.stack[32] == 0x1b8;
      var s10 := Add(s9);
      assert s10.stack[31] == 0x1b8;
      var s11 := PushN(s10, 2, 0x06d7);
      assert s11.stack[0] == 0x6d7;
      assert s11.stack[32] == 0x1b8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s12, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 82
    * Starting at 0x6ef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[31] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[31] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[30] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[29] == 0x1b8;
      var s4 := Pop(s3);
      assert s4.stack[28] == 0x1b8;
      var s5 := Pop(s4);
      assert s5.stack[27] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[27] == 0x1b8;
      var s7 := Pop(s6);
      assert s7.stack[26] == 0x1b8;
      var s8 := Swap(s7, 1);
      assert s8.stack[26] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[27] == 0x1b8;
      var s10 := Add(s9);
      assert s10.stack[26] == 0x1b8;
      var s11 := Swap(s10, 1);
      assert s11.stack[26] == 0x1b8;
      var s12 := PushN(s11, 1, 0x1f);
      assert s12.stack[27] == 0x1b8;
      var s13 := And(s12);
      assert s13.stack[26] == 0x1b8;
      var s14 := Dup(s13, 1);
      assert s14.stack[27] == 0x1b8;
      var s15 := IsZero(s14);
      assert s15.stack[27] == 0x1b8;
      var s16 := PushN(s15, 2, 0x071c);
      assert s16.stack[0] == 0x71c;
      assert s16.stack[28] == 0x1b8;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s17, gas - 1)
      else
        ExecuteFromCFGNode_s190(s17, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 83
    * Starting at 0x703
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x703 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[26] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[27] == 0x1b8;
      var s2 := Dup(s1, 3);
      assert s2.stack[28] == 0x1b8;
      var s3 := Sub(s2);
      assert s3.stack[27] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[28] == 0x1b8;
      var s5 := MLoad(s4);
      assert s5.stack[28] == 0x1b8;
      var s6 := PushN(s5, 1, 0x01);
      assert s6.stack[29] == 0x1b8;
      var s7 := Dup(s6, 4);
      assert s7.stack[30] == 0x1b8;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[31] == 0x1b8;
      var s9 := Sub(s8);
      assert s9.stack[30] == 0x1b8;
      var s10 := PushN(s9, 2, 0x0100);
      assert s10.stack[31] == 0x1b8;
      var s11 := Exp(s10);
      assert s11.stack[30] == 0x1b8;
      var s12 := Sub(s11);
      assert s12.stack[29] == 0x1b8;
      var s13 := Not(s12);
      assert s13.stack[29] == 0x1b8;
      var s14 := And(s13);
      assert s14.stack[28] == 0x1b8;
      var s15 := Dup(s14, 2);
      assert s15.stack[29] == 0x1b8;
      var s16 := MStore(s15);
      assert s16.stack[27] == 0x1b8;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[28] == 0x1b8;
      var s18 := Add(s17);
      assert s18.stack[27] == 0x1b8;
      var s19 := Swap(s18, 2);
      assert s19.stack[27] == 0x1b8;
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s191(s20, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 84
    * Starting at 0x71c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 26
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -12
    * Net Capacity Effect: +12
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[26] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[26] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[25] == 0x1b8;
      var s3 := Swap(s2, 14);
      assert s3.stack[25] == 0x1b8;
      var s4 := Pop(s3);
      assert s4.stack[24] == 0x1b8;
      var s5 := Pop(s4);
      assert s5.stack[23] == 0x1b8;
      var s6 := Pop(s5);
      assert s6.stack[22] == 0x1b8;
      var s7 := Pop(s6);
      assert s7.stack[21] == 0x1b8;
      var s8 := Pop(s7);
      assert s8.stack[20] == 0x1b8;
      var s9 := Pop(s8);
      assert s9.stack[19] == 0x1b8;
      var s10 := Pop(s9);
      assert s10.stack[18] == 0x1b8;
      var s11 := Pop(s10);
      assert s11.stack[17] == 0x1b8;
      var s12 := Pop(s11);
      assert s12.stack[16] == 0x1b8;
      var s13 := Pop(s12);
      assert s13.stack[15] == 0x1b8;
      var s14 := Pop(s13);
      assert s14.stack[14] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[13] == 0x1b8;
      var s16 := Pop(s15);
      assert s16.stack[12] == 0x1b8;
      var s17 := Pop(s16);
      assert s17.stack[11] == 0x1b8;
      var s18 := PushN(s17, 1, 0x40);
      assert s18.stack[12] == 0x1b8;
      var s19 := MLoad(s18);
      assert s19.stack[12] == 0x1b8;
      var s20 := Dup(s19, 1);
      assert s20.stack[13] == 0x1b8;
      var s21 := Swap(s20, 2);
      assert s21.stack[13] == 0x1b8;
      var s22 := Sub(s21);
      assert s22.stack[12] == 0x1b8;
      var s23 := Swap(s22, 1);
      assert s23.stack[12] == 0x1b8;
      var s24 := LogN(s23, 1);
      assert s24.stack[9] == 0x1b8;
      var s25 := PushN(s24, 1, 0x00);
      assert s25.stack[10] == 0x1b8;
      var s26 := PushN(s25, 1, 0x02);
      assert s26.stack[11] == 0x1b8;
      var s27 := Dup(s26, 11);
      assert s27.stack[12] == 0x1b8;
      var s28 := Dup(s27, 11);
      assert s28.stack[13] == 0x1b8;
      var s29 := PushN(s28, 1, 0x00);
      assert s29.stack[14] == 0x1b8;
      var s30 := PushN(s29, 1, 0x80);
      assert s30.stack[15] == 0x1b8;
      var s31 := Shl(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s192(s31, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 85
    * Starting at 0x740
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x740 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[15] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[15] == 0x1b8;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[16] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[15] == 0x1b8;
      var s5 := Dup(s4, 1);
      assert s5.stack[16] == 0x1b8;
      var s6 := Dup(s5, 5);
      assert s6.stack[17] == 0x1b8;
      var s7 := Dup(s6, 5);
      assert s7.stack[18] == 0x1b8;
      var s8 := Dup(s7, 1);
      assert s8.stack[19] == 0x1b8;
      var s9 := Dup(s8, 3);
      assert s9.stack[20] == 0x1b8;
      var s10 := Dup(s9, 5);
      assert s10.stack[21] == 0x1b8;
      var s11 := CallDataCopy(s10);
      assert s11.stack[18] == 0x1b8;
      var s12 := PushN(s11, 32, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000);
      assert s12.stack[19] == 0x1b8;
      var s13 := Swap(s12, 1);
      assert s13.stack[19] == 0x1b8;
      var s14 := Swap(s13, 5);
      assert s14.stack[19] == 0x1b8;
      var s15 := And(s14);
      assert s15.stack[18] == 0x1b8;
      var s16 := Swap(s15, 2);
      assert s16.stack[18] == 0x1b8;
      var s17 := Swap(s16, 1);
      assert s17.stack[18] == 0x1b8;
      var s18 := Swap(s17, 4);
      assert s18.stack[18] == 0x1b8;
      var s19 := Add(s18);
      assert s19.stack[17] == 0x1b8;
      var s20 := Swap(s19, 1);
      assert s20.stack[17] == 0x1b8;
      var s21 := Dup(s20, 2);
      assert s21.stack[18] == 0x1b8;
      var s22 := MStore(s21);
      assert s22.stack[16] == 0x1b8;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[17] == 0x1b8;
      var s24 := Dup(s23, 1);
      assert s24.stack[18] == 0x1b8;
      var s25 := MLoad(s24);
      assert s25.stack[18] == 0x1b8;
      var s26 := PushN(s25, 32, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0);
      assert s26.stack[19] == 0x1b8;
      var s27 := Dup(s26, 2);
      assert s27.stack[20] == 0x1b8;
      var s28 := Dup(s27, 5);
      assert s28.stack[21] == 0x1b8;
      var s29 := Sub(s28);
      assert s29.stack[20] == 0x1b8;
      var s30 := Add(s29);
      assert s30.stack[19] == 0x1b8;
      var s31 := Dup(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s193(s31, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 86
    * Starting at 0x7a2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[20] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.stack[18] == 0x1b8;
      var s2 := PushN(s1, 1, 0x10);
      assert s2.stack[19] == 0x1b8;
      var s3 := Swap(s2, 1);
      assert s3.stack[19] == 0x1b8;
      var s4 := Swap(s3, 3);
      assert s4.stack[19] == 0x1b8;
      var s5 := Add(s4);
      assert s5.stack[18] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[18] == 0x1b8;
      var s7 := Dup(s6, 2);
      assert s7.stack[19] == 0x1b8;
      var s8 := Swap(s7, 1);
      assert s8.stack[19] == 0x1b8;
      var s9 := MStore(s8);
      assert s9.stack[17] == 0x1b8;
      var s10 := Dup(s9, 2);
      assert s10.stack[18] == 0x1b8;
      var s11 := MLoad(s10);
      assert s11.stack[18] == 0x1b8;
      var s12 := Swap(s11, 2);
      assert s12.stack[18] == 0x1b8;
      var s13 := Swap(s12, 6);
      assert s13.stack[18] == 0x1b8;
      var s14 := Pop(s13);
      assert s14.stack[17] == 0x1b8;
      var s15 := Swap(s14, 4);
      assert s15.stack[17] == 0x1b8;
      var s16 := Pop(s15);
      assert s16.stack[16] == 0x1b8;
      var s17 := Dup(s16, 4);
      assert s17.stack[17] == 0x1b8;
      var s18 := Swap(s17, 3);
      assert s18.stack[17] == 0x1b8;
      var s19 := Pop(s18);
      assert s19.stack[16] == 0x1b8;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[17] == 0x1b8;
      var s21 := Dup(s20, 6);
      assert s21.stack[18] == 0x1b8;
      var s22 := Add(s21);
      assert s22.stack[17] == 0x1b8;
      var s23 := Swap(s22, 2);
      assert s23.stack[17] == 0x1b8;
      var s24 := Pop(s23);
      assert s24.stack[16] == 0x1b8;
      var s25 := Dup(s24, 1);
      assert s25.stack[17] == 0x1b8;
      var s26 := Dup(s25, 4);
      assert s26.stack[18] == 0x1b8;
      var s27 := Dup(s26, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s194(s27, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 87
    * Starting at 0x7bf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[19] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[19] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[20] == 0x1b8;
      var s3 := Dup(s2, 4);
      assert s3.stack[21] == 0x1b8;
      var s4 := Lt(s3);
      assert s4.stack[20] == 0x1b8;
      var s5 := PushN(s4, 2, 0x07fc);
      assert s5.stack[0] == 0x7fc;
      assert s5.stack[21] == 0x1b8;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s196(s6, gas - 1)
      else
        ExecuteFromCFGNode_s195(s6, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 88
    * Starting at 0x7c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[19] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[20] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[20] == 0x1b8;
      var s3 := Dup(s2, 3);
      assert s3.stack[21] == 0x1b8;
      var s4 := MStore(s3);
      assert s4.stack[19] == 0x1b8;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[20] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[20] == 0x1b8;
      var s7 := Swap(s6, 3);
      assert s7.stack[20] == 0x1b8;
      var s8 := Add(s7);
      assert s8.stack[19] == 0x1b8;
      var s9 := Swap(s8, 2);
      assert s9.stack[19] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[20] == 0x1b8;
      var s11 := Swap(s10, 2);
      assert s11.stack[20] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[21] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[20] == 0x1b8;
      var s14 := Swap(s13, 2);
      assert s14.stack[20] == 0x1b8;
      var s15 := Add(s14);
      assert s15.stack[19] == 0x1b8;
      var s16 := PushN(s15, 2, 0x07bf);
      assert s16.stack[0] == 0x7bf;
      assert s16.stack[20] == 0x1b8;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s17, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 89
    * Starting at 0x7fc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[19] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[19] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[19] == 0x1b8;
      var s3 := Dup(s2, 2);
      assert s3.stack[20] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[20] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[21] == 0x1b8;
      var s6 := Swap(s5, 4);
      assert s6.stack[21] == 0x1b8;
      var s7 := Dup(s6, 5);
      assert s7.stack[22] == 0x1b8;
      var s8 := Sub(s7);
      assert s8.stack[21] == 0x1b8;
      var s9 := PushN(s8, 2, 0x0100);
      assert s9.stack[22] == 0x1b8;
      var s10 := Exp(s9);
      assert s10.stack[21] == 0x1b8;
      var s11 := PushN(s10, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s11.stack[22] == 0x1b8;
      var s12 := Add(s11);
      assert s12.stack[21] == 0x1b8;
      var s13 := Dup(s12, 1);
      assert s13.stack[22] == 0x1b8;
      var s14 := Not(s13);
      assert s14.stack[22] == 0x1b8;
      var s15 := Swap(s14, 1);
      assert s15.stack[22] == 0x1b8;
      var s16 := Swap(s15, 3);
      assert s16.stack[22] == 0x1b8;
      var s17 := And(s16);
      assert s17.stack[21] == 0x1b8;
      var s18 := Swap(s17, 2);
      assert s18.stack[21] == 0x1b8;
      var s19 := And(s18);
      assert s19.stack[20] == 0x1b8;
      var s20 := Or(s19);
      assert s20.stack[19] == 0x1b8;
      var s21 := Swap(s20, 1);
      assert s21.stack[19] == 0x1b8;
      var s22 := MStore(s21);
      assert s22.stack[17] == 0x1b8;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[18] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[18] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[18] == 0x1b8;
      var s26 := Swap(s25, 1);
      assert s26.stack[18] == 0x1b8;
      var s27 := Swap(s26, 4);
      assert s27.stack[18] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[17] == 0x1b8;
      var s29 := Swap(s28, 5);
      assert s29.stack[17] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[16] == 0x1b8;
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s197(s31, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 90
    * Starting at 0x83f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[16] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[15] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[14] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[15] == 0x1b8;
      var s5 := Dup(s4, 4);
      assert s5.stack[16] == 0x1b8;
      var s6 := Sub(s5);
      assert s6.stack[15] == 0x1b8;
      var s7 := Dup(s6, 2);
      assert s7.stack[16] == 0x1b8;
      var s8 := Dup(s7, 6);
      assert s8.stack[17] == 0x1b8;
      var s9 := Gas(s8);
      assert s9.stack[18] == 0x1b8; 
      var s10 := StaticCall(s9);
      assert s10.stack[13] == 0x1b8;
      var s11 := IsZero(s10);
      assert s11.stack[13] == 0x1b8;
      var s12 := Dup(s11, 1);
      assert s12.stack[14] == 0x1b8;
      var s13 := IsZero(s12);
      assert s13.stack[14] == 0x1b8;
      var s14 := PushN(s13, 2, 0x0859);
      assert s14.stack[0] == 0x859;
      assert s14.stack[15] == 0x1b8;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s15, gas - 1)
      else
        ExecuteFromCFGNode_s198(s15, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 91
    * Starting at 0x850
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x850 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.stack[14] == 0x1b8;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[15] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[16] == 0x1b8;
      var s4 := ReturnDataCopy(s3);
      assert s4.stack[13] == 0x1b8;
      var s5 := ReturnDataSize(s4);
      assert s5.stack[14] == 0x1b8;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[15] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 199
    * Segment Id for this node is: 92
    * Starting at 0x859
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x859 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[13] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[12] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[11] == 0x1b8;
      var s4 := Pop(s3);
      assert s4.stack[10] == 0x1b8;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[11] == 0x1b8;
      var s6 := MLoad(s5);
      assert s6.stack[11] == 0x1b8;
      var s7 := ReturnDataSize(s6); 
      assert s7.stack[12] == 0x1b8;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[13] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[14] == 0x1b8;
      var s10 := Lt(s9);
      assert s10.stack[13] == 0x1b8;
      var s11 := IsZero(s10);
      assert s11.stack[13] == 0x1b8;
      var s12 := PushN(s11, 2, 0x086e);
      assert s12.stack[0] == 0x86e;
      assert s12.stack[14] == 0x1b8;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s13, gas - 1)
      else
        ExecuteFromCFGNode_s200(s13, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 93
    * Starting at 0x86a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[13] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[14] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 201
    * Segment Id for this node is: 94
    * Starting at 0x86e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[12] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[11] == 0x1b8;
      var s3 := MLoad(s2);
      assert s3.stack[11] == 0x1b8;
      var s4 := Swap(s3, 1);
      assert s4.stack[11] == 0x1b8;
      var s5 := Pop(s4);
      assert s5.stack[10] == 0x1b8;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[11] == 0x1b8;
      var s7 := PushN(s6, 1, 0x02);
      assert s7.stack[12] == 0x1b8;
      var s8 := Dup(s7, 1);
      assert s8.stack[13] == 0x1b8;
      var s9 := PushN(s8, 2, 0x0884);
      assert s9.stack[0] == 0x884;
      assert s9.stack[14] == 0x1b8;
      var s10 := PushN(s9, 1, 0x40);
      assert s10.stack[1] == 0x884;
      assert s10.stack[15] == 0x1b8;
      var s11 := Dup(s10, 5);
      assert s11.stack[2] == 0x884;
      assert s11.stack[16] == 0x1b8;
      var s12 := Dup(s11, 11);
      assert s12.stack[3] == 0x884;
      assert s12.stack[17] == 0x1b8;
      var s13 := Dup(s12, 13);
      assert s13.stack[4] == 0x884;
      assert s13.stack[18] == 0x1b8;
      var s14 := PushN(s13, 2, 0x16fe);
      assert s14.stack[0] == 0x16fe;
      assert s14.stack[5] == 0x884;
      assert s14.stack[19] == 0x1b8;
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s15, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 244
    * Starting at 0x16fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x884

    requires s0.stack[18] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x884;
      assert s1.stack[18] == 0x1b8;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[5] == 0x884;
      assert s2.stack[19] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[6] == 0x884;
      assert s3.stack[20] == 0x1b8;
      var s4 := Dup(s3, 6);
      assert s4.stack[7] == 0x884;
      assert s4.stack[21] == 0x1b8;
      var s5 := Dup(s4, 6);
      assert s5.stack[8] == 0x884;
      assert s5.stack[22] == 0x1b8;
      var s6 := Gt(s5);
      assert s6.stack[7] == 0x884;
      assert s6.stack[21] == 0x1b8;
      var s7 := IsZero(s6);
      assert s7.stack[7] == 0x884;
      assert s7.stack[21] == 0x1b8;
      var s8 := PushN(s7, 2, 0x170d);
      assert s8.stack[0] == 0x170d;
      assert s8.stack[8] == 0x884;
      assert s8.stack[22] == 0x1b8;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s9, gas - 1)
      else
        ExecuteFromCFGNode_s203(s9, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 245
    * Starting at 0x170a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x170a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x884

    requires s0.stack[20] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[7] == 0x884;
      assert s1.stack[21] == 0x1b8;
      var s2 := Dup(s1, 3);
      assert s2.stack[8] == 0x884;
      assert s2.stack[22] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 204
    * Segment Id for this node is: 246
    * Starting at 0x170d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x170d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x884

    requires s0.stack[20] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x884;
      assert s1.stack[20] == 0x1b8;
      var s2 := Dup(s1, 4);
      assert s2.stack[7] == 0x884;
      assert s2.stack[21] == 0x1b8;
      var s3 := Dup(s2, 7);
      assert s3.stack[8] == 0x884;
      assert s3.stack[22] == 0x1b8;
      var s4 := Gt(s3);
      assert s4.stack[7] == 0x884;
      assert s4.stack[21] == 0x1b8;
      var s5 := IsZero(s4);
      assert s5.stack[7] == 0x884;
      assert s5.stack[21] == 0x1b8;
      var s6 := PushN(s5, 2, 0x1719);
      assert s6.stack[0] == 0x1719;
      assert s6.stack[8] == 0x884;
      assert s6.stack[22] == 0x1b8;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s7, gas - 1)
      else
        ExecuteFromCFGNode_s205(s7, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 247
    * Starting at 0x1716
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1716 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x884

    requires s0.stack[20] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[7] == 0x884;
      assert s1.stack[21] == 0x1b8;
      var s2 := Dup(s1, 3);
      assert s2.stack[8] == 0x884;
      assert s2.stack[22] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 206
    * Segment Id for this node is: 248
    * Starting at 0x1719
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1719 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x884

    requires s0.stack[20] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x884;
      assert s1.stack[20] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[5] == 0x884;
      assert s2.stack[19] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[4] == 0x884;
      assert s3.stack[18] == 0x1b8;
      var s4 := Dup(s3, 3);
      assert s4.stack[5] == 0x884;
      assert s4.stack[19] == 0x1b8;
      var s5 := Add(s4);
      assert s5.stack[4] == 0x884;
      assert s5.stack[18] == 0x1b8;
      var s6 := Swap(s5, 4);
      assert s6.stack[0] == 0x884;
      assert s6.stack[18] == 0x1b8;
      var s7 := Swap(s6, 2);
      assert s7.stack[2] == 0x884;
      assert s7.stack[18] == 0x1b8;
      var s8 := Swap(s7, 1);
      assert s8.stack[2] == 0x884;
      assert s8.stack[18] == 0x1b8;
      var s9 := Swap(s8, 3);
      assert s9.stack[2] == 0x884;
      assert s9.stack[18] == 0x1b8;
      var s10 := Sub(s9);
      assert s10.stack[1] == 0x884;
      assert s10.stack[17] == 0x1b8;
      var s11 := Swap(s10, 2);
      assert s11.stack[1] == 0x884;
      assert s11.stack[17] == 0x1b8;
      var s12 := Pop(s11);
      assert s12.stack[0] == 0x884;
      assert s12.stack[16] == 0x1b8;
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s13, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 95
    * Starting at 0x884
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x884 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[15] == 0x1b8;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[16] == 0x1b8;
      var s3 := MLoad(s2);
      assert s3.stack[16] == 0x1b8;
      var s4 := PushN(s3, 1, 0x20);
      assert s4.stack[17] == 0x1b8;
      var s5 := Add(s4);
      assert s5.stack[16] == 0x1b8;
      var s6 := Dup(s5, 1);
      assert s6.stack[17] == 0x1b8;
      var s7 := Dup(s6, 4);
      assert s7.stack[18] == 0x1b8;
      var s8 := Dup(s7, 4);
      assert s8.stack[19] == 0x1b8;
      var s9 := Dup(s8, 1);
      assert s9.stack[20] == 0x1b8;
      var s10 := Dup(s9, 3);
      assert s10.stack[21] == 0x1b8;
      var s11 := Dup(s10, 5);
      assert s11.stack[22] == 0x1b8;
      var s12 := CallDataCopy(s11);
      assert s12.stack[19] == 0x1b8;
      var s13 := Dup(s12, 1);
      assert s13.stack[20] == 0x1b8;
      var s14 := Dup(s13, 4);
      assert s14.stack[21] == 0x1b8;
      var s15 := Add(s14);
      assert s15.stack[20] == 0x1b8;
      var s16 := Swap(s15, 3);
      assert s16.stack[20] == 0x1b8;
      var s17 := Pop(s16);
      assert s17.stack[19] == 0x1b8;
      var s18 := Pop(s17);
      assert s18.stack[18] == 0x1b8;
      var s19 := Pop(s18);
      assert s19.stack[17] == 0x1b8;
      var s20 := Swap(s19, 3);
      assert s20.stack[17] == 0x1b8;
      var s21 := Pop(s20);
      assert s21.stack[16] == 0x1b8;
      var s22 := Pop(s21);
      assert s22.stack[15] == 0x1b8;
      var s23 := Pop(s22);
      assert s23.stack[14] == 0x1b8;
      var s24 := PushN(s23, 1, 0x40);
      assert s24.stack[15] == 0x1b8;
      var s25 := MLoad(s24);
      assert s25.stack[15] == 0x1b8;
      var s26 := PushN(s25, 1, 0x20);
      assert s26.stack[16] == 0x1b8;
      var s27 := Dup(s26, 2);
      assert s27.stack[17] == 0x1b8;
      var s28 := Dup(s27, 4);
      assert s28.stack[18] == 0x1b8;
      var s29 := Sub(s28);
      assert s29.stack[17] == 0x1b8;
      var s30 := Sub(s29);
      assert s30.stack[16] == 0x1b8;
      var s31 := Dup(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s208(s31, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 96
    * Starting at 0x8a7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[17] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.stack[15] == 0x1b8;
      var s2 := Swap(s1, 1);
      assert s2.stack[15] == 0x1b8;
      var s3 := PushN(s2, 1, 0x40);
      assert s3.stack[16] == 0x1b8;
      var s4 := MStore(s3);
      assert s4.stack[14] == 0x1b8;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[15] == 0x1b8;
      var s6 := MLoad(s5);
      assert s6.stack[15] == 0x1b8;
      var s7 := Dup(s6, 1);
      assert s7.stack[16] == 0x1b8;
      var s8 := Dup(s7, 3);
      assert s8.stack[17] == 0x1b8;
      var s9 := Dup(s8, 1);
      assert s9.stack[18] == 0x1b8;
      var s10 := MLoad(s9);
      assert s10.stack[18] == 0x1b8;
      var s11 := Swap(s10, 1);
      assert s11.stack[18] == 0x1b8;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[19] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[18] == 0x1b8;
      var s14 := Swap(s13, 1);
      assert s14.stack[18] == 0x1b8;
      var s15 := Dup(s14, 1);
      assert s15.stack[19] == 0x1b8;
      var s16 := Dup(s15, 4);
      assert s16.stack[20] == 0x1b8;
      var s17 := Dup(s16, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s209(s17, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 97
    * Starting at 0x8bb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[21] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[21] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[22] == 0x1b8;
      var s3 := Dup(s2, 4);
      assert s3.stack[23] == 0x1b8;
      var s4 := Lt(s3);
      assert s4.stack[22] == 0x1b8;
      var s5 := PushN(s4, 2, 0x08f8);
      assert s5.stack[0] == 0x8f8;
      assert s5.stack[23] == 0x1b8;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s211(s6, gas - 1)
      else
        ExecuteFromCFGNode_s210(s6, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 98
    * Starting at 0x8c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[21] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[22] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[22] == 0x1b8;
      var s3 := Dup(s2, 3);
      assert s3.stack[23] == 0x1b8;
      var s4 := MStore(s3);
      assert s4.stack[21] == 0x1b8;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[22] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[22] == 0x1b8;
      var s7 := Swap(s6, 3);
      assert s7.stack[22] == 0x1b8;
      var s8 := Add(s7);
      assert s8.stack[21] == 0x1b8;
      var s9 := Swap(s8, 2);
      assert s9.stack[21] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[22] == 0x1b8;
      var s11 := Swap(s10, 2);
      assert s11.stack[22] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[23] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[22] == 0x1b8;
      var s14 := Swap(s13, 2);
      assert s14.stack[22] == 0x1b8;
      var s15 := Add(s14);
      assert s15.stack[21] == 0x1b8;
      var s16 := PushN(s15, 2, 0x08bb);
      assert s16.stack[0] == 0x8bb;
      assert s16.stack[22] == 0x1b8;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s17, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 99
    * Starting at 0x8f8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[21] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[21] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[21] == 0x1b8;
      var s3 := Dup(s2, 2);
      assert s3.stack[22] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[22] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[23] == 0x1b8;
      var s6 := Swap(s5, 4);
      assert s6.stack[23] == 0x1b8;
      var s7 := Dup(s6, 5);
      assert s7.stack[24] == 0x1b8;
      var s8 := Sub(s7);
      assert s8.stack[23] == 0x1b8;
      var s9 := PushN(s8, 2, 0x0100);
      assert s9.stack[24] == 0x1b8;
      var s10 := Exp(s9);
      assert s10.stack[23] == 0x1b8;
      var s11 := PushN(s10, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s11.stack[24] == 0x1b8;
      var s12 := Add(s11);
      assert s12.stack[23] == 0x1b8;
      var s13 := Dup(s12, 1);
      assert s13.stack[24] == 0x1b8;
      var s14 := Not(s13);
      assert s14.stack[24] == 0x1b8;
      var s15 := Swap(s14, 1);
      assert s15.stack[24] == 0x1b8;
      var s16 := Swap(s15, 3);
      assert s16.stack[24] == 0x1b8;
      var s17 := And(s16);
      assert s17.stack[23] == 0x1b8;
      var s18 := Swap(s17, 2);
      assert s18.stack[23] == 0x1b8;
      var s19 := And(s18);
      assert s19.stack[22] == 0x1b8;
      var s20 := Or(s19);
      assert s20.stack[21] == 0x1b8; 
      var s21 := Swap(s20, 1);
      assert s21.stack[21] == 0x1b8;
      var s22 := MStore(s21);
      assert s22.stack[19] == 0x1b8;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[20] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[20] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[20] == 0x1b8;
      var s26 := Swap(s25, 1);
      assert s26.stack[20] == 0x1b8;
      var s27 := Swap(s26, 4);
      assert s27.stack[20] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[19] == 0x1b8;
      var s29 := Swap(s28, 5);
      assert s29.stack[19] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[18] == 0x1b8;
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s212(s31, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 100
    * Starting at 0x93b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[18] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[18] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[17] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[16] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[17] == 0x1b8;
      var s5 := Dup(s4, 4);
      assert s5.stack[18] == 0x1b8;
      var s6 := Sub(s5);
      assert s6.stack[17] == 0x1b8;
      var s7 := Dup(s6, 2);
      assert s7.stack[18] == 0x1b8;
      var s8 := Dup(s7, 6);
      assert s8.stack[19] == 0x1b8;
      var s9 := Gas(s8);
      assert s9.stack[20] == 0x1b8;
      var s10 := StaticCall(s9);
      assert s10.stack[15] == 0x1b8;
      var s11 := IsZero(s10);
      assert s11.stack[15] == 0x1b8;
      var s12 := Dup(s11, 1);
      assert s12.stack[16] == 0x1b8;
      var s13 := IsZero(s12);
      assert s13.stack[16] == 0x1b8;
      var s14 := PushN(s13, 2, 0x0955);
      assert s14.stack[0] == 0x955;
      assert s14.stack[17] == 0x1b8;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s214(s15, gas - 1)
      else
        ExecuteFromCFGNode_s213(s15, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 101
    * Starting at 0x94c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.stack[16] == 0x1b8;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[17] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[18] == 0x1b8;
      var s4 := ReturnDataCopy(s3);
      assert s4.stack[15] == 0x1b8;
      var s5 := ReturnDataSize(s4);
      assert s5.stack[16] == 0x1b8;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[17] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 214
    * Segment Id for this node is: 102
    * Starting at 0x955
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x955 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[15] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[14] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[13] == 0x1b8;
      var s4 := Pop(s3);
      assert s4.stack[12] == 0x1b8;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[13] == 0x1b8;
      var s6 := MLoad(s5);
      assert s6.stack[13] == 0x1b8;
      var s7 := ReturnDataSize(s6);
      assert s7.stack[14] == 0x1b8;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[15] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[16] == 0x1b8;
      var s10 := Lt(s9);
      assert s10.stack[15] == 0x1b8;
      var s11 := IsZero(s10);
      assert s11.stack[15] == 0x1b8;
      var s12 := PushN(s11, 2, 0x096a);
      assert s12.stack[0] == 0x96a;
      assert s12.stack[16] == 0x1b8;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s216(s13, gas - 1)
      else
        ExecuteFromCFGNode_s215(s13, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 103
    * Starting at 0x966
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x966 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[15] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[16] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 216
    * Segment Id for this node is: 104
    * Starting at 0x96a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[14] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[13] == 0x1b8;
      var s3 := MLoad(s2);
      assert s3.stack[13] == 0x1b8;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[14] == 0x1b8;
      var s5 := PushN(s4, 2, 0x097b);
      assert s5.stack[0] == 0x97b;
      assert s5.stack[15] == 0x1b8;
      var s6 := Dup(s5, 10);
      assert s6.stack[1] == 0x97b;
      assert s6.stack[16] == 0x1b8;
      var s7 := PushN(s6, 1, 0x40);
      assert s7.stack[2] == 0x97b;
      assert s7.stack[17] == 0x1b8;
      var s8 := Dup(s7, 2);
      assert s8.stack[3] == 0x97b;
      assert s8.stack[18] == 0x1b8;
      var s9 := Dup(s8, 14);
      assert s9.stack[4] == 0x97b;
      assert s9.stack[19] == 0x1b8;
      var s10 := PushN(s9, 2, 0x16fe);
      assert s10.stack[0] == 0x16fe;
      assert s10.stack[5] == 0x97b;
      assert s10.stack[20] == 0x1b8;
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s11, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 244
    * Starting at 0x16fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0x97b

    requires s0.stack[19] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x97b;
      assert s1.stack[19] == 0x1b8;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[5] == 0x97b;
      assert s2.stack[20] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[6] == 0x97b;
      assert s3.stack[21] == 0x1b8;
      var s4 := Dup(s3, 6);
      assert s4.stack[7] == 0x97b;
      assert s4.stack[22] == 0x1b8;
      var s5 := Dup(s4, 6);
      assert s5.stack[8] == 0x97b;
      assert s5.stack[23] == 0x1b8;
      var s6 := Gt(s5);
      assert s6.stack[7] == 0x97b;
      assert s6.stack[22] == 0x1b8;
      var s7 := IsZero(s6);
      assert s7.stack[7] == 0x97b;
      assert s7.stack[22] == 0x1b8;
      var s8 := PushN(s7, 2, 0x170d);
      assert s8.stack[0] == 0x170d;
      assert s8.stack[8] == 0x97b;
      assert s8.stack[23] == 0x1b8;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s219(s9, gas - 1)
      else
        ExecuteFromCFGNode_s218(s9, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 245
    * Starting at 0x170a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x170a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[6] == 0x97b

    requires s0.stack[21] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[7] == 0x97b;
      assert s1.stack[22] == 0x1b8;
      var s2 := Dup(s1, 3);
      assert s2.stack[8] == 0x97b;
      assert s2.stack[23] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 219
    * Segment Id for this node is: 246
    * Starting at 0x170d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x170d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[6] == 0x97b

    requires s0.stack[21] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x97b;
      assert s1.stack[21] == 0x1b8;
      var s2 := Dup(s1, 4);
      assert s2.stack[7] == 0x97b;
      assert s2.stack[22] == 0x1b8;
      var s3 := Dup(s2, 7);
      assert s3.stack[8] == 0x97b;
      assert s3.stack[23] == 0x1b8;
      var s4 := Gt(s3);
      assert s4.stack[7] == 0x97b;
      assert s4.stack[22] == 0x1b8;
      var s5 := IsZero(s4);
      assert s5.stack[7] == 0x97b;
      assert s5.stack[22] == 0x1b8;
      var s6 := PushN(s5, 2, 0x1719);
      assert s6.stack[0] == 0x1719;
      assert s6.stack[8] == 0x97b;
      assert s6.stack[23] == 0x1b8;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s221(s7, gas - 1)
      else
        ExecuteFromCFGNode_s220(s7, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 247
    * Starting at 0x1716
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1716 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[6] == 0x97b

    requires s0.stack[21] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[7] == 0x97b;
      assert s1.stack[22] == 0x1b8;
      var s2 := Dup(s1, 3);
      assert s2.stack[8] == 0x97b;
      assert s2.stack[23] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 221
    * Segment Id for this node is: 248
    * Starting at 0x1719
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1719 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[6] == 0x97b

    requires s0.stack[21] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x97b;
      assert s1.stack[21] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[5] == 0x97b;
      assert s2.stack[20] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[4] == 0x97b;
      assert s3.stack[19] == 0x1b8;
      var s4 := Dup(s3, 3);
      assert s4.stack[5] == 0x97b;
      assert s4.stack[20] == 0x1b8;
      var s5 := Add(s4);
      assert s5.stack[4] == 0x97b;
      assert s5.stack[19] == 0x1b8;
      var s6 := Swap(s5, 4);
      assert s6.stack[0] == 0x97b;
      assert s6.stack[19] == 0x1b8;
      var s7 := Swap(s6, 2);
      assert s7.stack[2] == 0x97b;
      assert s7.stack[19] == 0x1b8;
      var s8 := Swap(s7, 1);
      assert s8.stack[2] == 0x97b;
      assert s8.stack[19] == 0x1b8;
      var s9 := Swap(s8, 3);
      assert s9.stack[2] == 0x97b;
      assert s9.stack[19] == 0x1b8;
      var s10 := Sub(s9);
      assert s10.stack[1] == 0x97b;
      assert s10.stack[18] == 0x1b8;
      var s11 := Swap(s10, 2);
      assert s11.stack[1] == 0x97b;
      assert s11.stack[18] == 0x1b8;
      var s12 := Pop(s11);
      assert s12.stack[0] == 0x97b;
      assert s12.stack[17] == 0x1b8;
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s13, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 105
    * Starting at 0x97b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[16] == 0x1b8;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[17] == 0x1b8;
      var s3 := MLoad(s2);
      assert s3.stack[17] == 0x1b8;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[18] == 0x1b8;
      var s5 := Swap(s4, 1);
      assert s5.stack[18] == 0x1b8;
      var s6 := PushN(s5, 1, 0x20);
      assert s6.stack[19] == 0x1b8;
      var s7 := Add(s6);
      assert s7.stack[18] == 0x1b8;
      var s8 := Dup(s7, 1);
      assert s8.stack[19] == 0x1b8;
      var s9 := Dup(s8, 5);
      assert s9.stack[20] == 0x1b8;
      var s10 := Dup(s9, 5);
      assert s10.stack[21] == 0x1b8;
      var s11 := Dup(s10, 1);
      assert s11.stack[22] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[23] == 0x1b8;
      var s13 := Dup(s12, 5);
      assert s13.stack[24] == 0x1b8;
      var s14 := CallDataCopy(s13);
      assert s14.stack[21] == 0x1b8;
      var s15 := Swap(s14, 2);
      assert s15.stack[21] == 0x1b8;
      var s16 := Swap(s15, 1);
      assert s16.stack[21] == 0x1b8;
      var s17 := Swap(s16, 2);
      assert s17.stack[21] == 0x1b8;
      var s18 := Add(s17);
      assert s18.stack[20] == 0x1b8;
      var s19 := Swap(s18, 3);
      assert s19.stack[20] == 0x1b8;
      var s20 := Dup(s19, 4);
      assert s20.stack[21] == 0x1b8;
      var s21 := MStore(s20);
      assert s21.stack[19] == 0x1b8;
      var s22 := Pop(s21);
      assert s22.stack[18] == 0x1b8;
      var s23 := Pop(s22);
      assert s23.stack[17] == 0x1b8;
      var s24 := PushN(s23, 1, 0x40);
      assert s24.stack[18] == 0x1b8;
      var s25 := Dup(s24, 1);
      assert s25.stack[19] == 0x1b8;
      var s26 := MLoad(s25);
      assert s26.stack[19] == 0x1b8;
      var s27 := Dup(s26, 1);
      assert s27.stack[20] == 0x1b8;
      var s28 := Dup(s27, 4);
      assert s28.stack[21] == 0x1b8;
      var s29 := Sub(s28);
      assert s29.stack[20] == 0x1b8;
      var s30 := Dup(s29, 2);
      assert s30.stack[21] == 0x1b8;
      var s31 := MStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s223(s31, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 106
    * Starting at 0x99e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[19] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      assert s1.stack[20] == 0x1b8;
      var s2 := Swap(s1, 3);
      assert s2.stack[20] == 0x1b8;
      var s3 := Dup(s2, 4);
      assert s3.stack[21] == 0x1b8;
      var s4 := Add(s3);
      assert s4.stack[20] == 0x1b8;
      var s5 := Swap(s4, 2);
      assert s5.stack[20] == 0x1b8;
      var s6 := Dup(s5, 3);
      assert s6.stack[21] == 0x1b8;
      var s7 := Swap(s6, 1);
      assert s7.stack[21] == 0x1b8;
      var s8 := MStore(s7);
      assert s8.stack[19] == 0x1b8;
      var s9 := Dup(s8, 1);
      assert s9.stack[20] == 0x1b8;
      var s10 := MLoad(s9);
      assert s10.stack[20] == 0x1b8;
      var s11 := Swap(s10, 1);
      assert s11.stack[20] == 0x1b8;
      var s12 := Swap(s11, 5);
      assert s12.stack[20] == 0x1b8;
      var s13 := Pop(s12);
      assert s13.stack[19] == 0x1b8;
      var s14 := Swap(s13, 1);
      assert s14.stack[19] == 0x1b8;
      var s15 := Swap(s14, 3);
      assert s15.stack[19] == 0x1b8;
      var s16 := Pop(s15);
      assert s16.stack[18] == 0x1b8;
      var s17 := Dup(s16, 3);
      assert s17.stack[19] == 0x1b8;
      var s18 := Swap(s17, 2);
      assert s18.stack[19] == 0x1b8;
      var s19 := Dup(s18, 5);
      assert s19.stack[20] == 0x1b8;
      var s20 := Add(s19);
      assert s20.stack[19] == 0x1b8;
      var s21 := Swap(s20, 1);
      assert s21.stack[19] == 0x1b8;
      var s22 := Dup(s21, 1);
      assert s22.stack[20] == 0x1b8;
      var s23 := Dup(s22, 4);
      assert s23.stack[21] == 0x1b8;
      var s24 := Dup(s23, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s224(s24, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 107
    * Starting at 0x9b7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[22] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[22] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[23] == 0x1b8;
      var s3 := Dup(s2, 4);
      assert s3.stack[24] == 0x1b8;
      var s4 := Lt(s3);
      assert s4.stack[23] == 0x1b8;
      var s5 := PushN(s4, 2, 0x09f4);
      assert s5.stack[0] == 0x9f4;
      assert s5.stack[24] == 0x1b8;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s226(s6, gas - 1)
      else
        ExecuteFromCFGNode_s225(s6, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 108
    * Starting at 0x9c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[22] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[23] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[23] == 0x1b8;
      var s3 := Dup(s2, 3);
      assert s3.stack[24] == 0x1b8;
      var s4 := MStore(s3);
      assert s4.stack[22] == 0x1b8;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[23] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[23] == 0x1b8;
      var s7 := Swap(s6, 3);
      assert s7.stack[23] == 0x1b8;
      var s8 := Add(s7);
      assert s8.stack[22] == 0x1b8;
      var s9 := Swap(s8, 2);
      assert s9.stack[22] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[23] == 0x1b8;
      var s11 := Swap(s10, 2);
      assert s11.stack[23] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[24] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[23] == 0x1b8;
      var s14 := Swap(s13, 2);
      assert s14.stack[23] == 0x1b8;
      var s15 := Add(s14);
      assert s15.stack[22] == 0x1b8;
      var s16 := PushN(s15, 2, 0x09b7);
      assert s16.stack[0] == 0x9b7;
      assert s16.stack[23] == 0x1b8;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s17, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 109
    * Starting at 0x9f4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[22] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[22] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[22] == 0x1b8;
      var s3 := Dup(s2, 2);
      assert s3.stack[23] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[23] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[24] == 0x1b8;
      var s6 := Swap(s5, 4);
      assert s6.stack[24] == 0x1b8;
      var s7 := Dup(s6, 5);
      assert s7.stack[25] == 0x1b8;
      var s8 := Sub(s7);
      assert s8.stack[24] == 0x1b8;
      var s9 := PushN(s8, 2, 0x0100);
      assert s9.stack[25] == 0x1b8;
      var s10 := Exp(s9);
      assert s10.stack[24] == 0x1b8;
      var s11 := PushN(s10, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s11.stack[25] == 0x1b8;
      var s12 := Add(s11);
      assert s12.stack[24] == 0x1b8;
      var s13 := Dup(s12, 1);
      assert s13.stack[25] == 0x1b8;
      var s14 := Not(s13);
      assert s14.stack[25] == 0x1b8;
      var s15 := Swap(s14, 1);
      assert s15.stack[25] == 0x1b8;
      var s16 := Swap(s15, 3);
      assert s16.stack[25] == 0x1b8;
      var s17 := And(s16);
      assert s17.stack[24] == 0x1b8;
      var s18 := Swap(s17, 2);
      assert s18.stack[24] == 0x1b8;
      var s19 := And(s18);
      assert s19.stack[23] == 0x1b8;
      var s20 := Or(s19);
      assert s20.stack[22] == 0x1b8;
      var s21 := Swap(s20, 1);
      assert s21.stack[22] == 0x1b8;
      var s22 := MStore(s21);
      assert s22.stack[20] == 0x1b8;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[21] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[21] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[21] == 0x1b8;
      var s26 := Swap(s25, 1);
      assert s26.stack[21] == 0x1b8;
      var s27 := Swap(s26, 4);
      assert s27.stack[21] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[20] == 0x1b8;
      var s29 := Swap(s28, 5);
      assert s29.stack[20] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[19] == 0x1b8;
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s227(s31, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 110
    * Starting at 0xa37
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[19] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[19] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[18] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[17] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[18] == 0x1b8;
      var s5 := Dup(s4, 4);
      assert s5.stack[19] == 0x1b8;
      var s6 := Sub(s5);
      assert s6.stack[18] == 0x1b8;
      var s7 := Dup(s6, 2);
      assert s7.stack[19] == 0x1b8;
      var s8 := Dup(s7, 6);
      assert s8.stack[20] == 0x1b8;
      var s9 := Gas(s8);
      assert s9.stack[21] == 0x1b8;
      var s10 := StaticCall(s9);
      assert s10.stack[16] == 0x1b8;
      var s11 := IsZero(s10);
      assert s11.stack[16] == 0x1b8;
      var s12 := Dup(s11, 1);
      assert s12.stack[17] == 0x1b8;
      var s13 := IsZero(s12);
      assert s13.stack[17] == 0x1b8;
      var s14 := PushN(s13, 2, 0x0a51);
      assert s14.stack[0] == 0xa51;
      assert s14.stack[18] == 0x1b8;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s229(s15, gas - 1)
      else
        ExecuteFromCFGNode_s228(s15, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 111
    * Starting at 0xa48
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.stack[17] == 0x1b8;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[18] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[19] == 0x1b8;
      var s4 := ReturnDataCopy(s3); 
      assert s4.stack[16] == 0x1b8;
      var s5 := ReturnDataSize(s4);
      assert s5.stack[17] == 0x1b8;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[18] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 229
    * Segment Id for this node is: 112
    * Starting at 0xa51
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa51 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[16] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[15] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[14] == 0x1b8;
      var s4 := Pop(s3);
      assert s4.stack[13] == 0x1b8;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[14] == 0x1b8;
      var s6 := MLoad(s5);
      assert s6.stack[14] == 0x1b8;
      var s7 := ReturnDataSize(s6);
      assert s7.stack[15] == 0x1b8;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[16] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[17] == 0x1b8;
      var s10 := Lt(s9);
      assert s10.stack[16] == 0x1b8;
      var s11 := IsZero(s10);
      assert s11.stack[16] == 0x1b8;
      var s12 := PushN(s11, 2, 0x0a66);
      assert s12.stack[0] == 0xa66;
      assert s12.stack[17] == 0x1b8;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s13, gas - 1)
      else
        ExecuteFromCFGNode_s230(s13, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 113
    * Starting at 0xa62
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[16] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[17] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 231
    * Segment Id for this node is: 114
    * Starting at 0xa66
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa66 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[15] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[14] == 0x1b8;
      var s3 := MLoad(s2);
      assert s3.stack[14] == 0x1b8;
      var s4 := PushN(s3, 1, 0x40);
      assert s4.stack[15] == 0x1b8;
      var s5 := Dup(s4, 1);
      assert s5.stack[16] == 0x1b8;
      var s6 := MLoad(s5);
      assert s6.stack[16] == 0x1b8;
      var s7 := PushN(s6, 1, 0x20);
      assert s7.stack[17] == 0x1b8;
      var s8 := Dup(s7, 2);
      assert s8.stack[18] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[19] == 0x1b8;
      var s10 := Add(s9);
      assert s10.stack[18] == 0x1b8;
      var s11 := Swap(s10, 5);
      assert s11.stack[18] == 0x1b8;
      var s12 := Swap(s11, 1);
      assert s12.stack[18] == 0x1b8;
      var s13 := Swap(s12, 5);
      assert s13.stack[18] == 0x1b8;
      var s14 := MStore(s13);
      assert s14.stack[16] == 0x1b8;
      var s15 := Dup(s14, 1);
      assert s15.stack[17] == 0x1b8;
      var s16 := Dup(s15, 3);
      assert s16.stack[18] == 0x1b8;
      var s17 := Add(s16);
      assert s17.stack[17] == 0x1b8;
      var s18 := Swap(s17, 3);
      assert s18.stack[17] == 0x1b8;
      var s19 := Swap(s18, 1);
      assert s19.stack[17] == 0x1b8;
      var s20 := Swap(s19, 3);
      assert s20.stack[17] == 0x1b8;
      var s21 := MStore(s20);
      assert s21.stack[15] == 0x1b8;
      var s22 := Dup(s21, 1);
      assert s22.stack[16] == 0x1b8;
      var s23 := MLoad(s22);
      assert s23.stack[16] == 0x1b8;
      var s24 := Dup(s23, 1);
      assert s24.stack[17] == 0x1b8;
      var s25 := Dup(s24, 4);
      assert s25.stack[18] == 0x1b8;
      var s26 := Sub(s25);
      assert s26.stack[17] == 0x1b8;
      var s27 := Dup(s26, 3);
      assert s27.stack[18] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[17] == 0x1b8;
      var s29 := Dup(s28, 2);
      assert s29.stack[18] == 0x1b8;
      var s30 := MStore(s29);
      assert s30.stack[16] == 0x1b8;
      var s31 := PushN(s30, 1, 0x60);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s232(s31, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 115
    * Starting at 0xa88
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[17] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[17] == 0x1b8;
      var s2 := Swap(s1, 3);
      assert s2.stack[17] == 0x1b8;
      var s3 := Add(s2);
      assert s3.stack[16] == 0x1b8;
      var s4 := Swap(s3, 1);
      assert s4.stack[16] == 0x1b8;
      var s5 := Dup(s4, 2);
      assert s5.stack[17] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[17] == 0x1b8;
      var s7 := MStore(s6);
      assert s7.stack[15] == 0x1b8;
      var s8 := Dup(s7, 2);
      assert s8.stack[16] == 0x1b8;
      var s9 := MLoad(s8);
      assert s9.stack[16] == 0x1b8;
      var s10 := Swap(s9, 2);
      assert s10.stack[16] == 0x1b8;
      var s11 := Swap(s10, 3);
      assert s11.stack[16] == 0x1b8;
      var s12 := Swap(s11, 1);
      assert s12.stack[16] == 0x1b8;
      var s13 := Swap(s12, 2);
      assert s13.stack[16] == 0x1b8;
      var s14 := Dup(s13, 3);
      assert s14.stack[17] == 0x1b8;
      var s15 := Swap(s14, 2);
      assert s15.stack[17] == 0x1b8;
      var s16 := Dup(s15, 5);
      assert s16.stack[18] == 0x1b8;
      var s17 := Add(s16);
      assert s17.stack[17] == 0x1b8;
      var s18 := Swap(s17, 1);
      assert s18.stack[17] == 0x1b8;
      var s19 := Dup(s18, 1);
      assert s19.stack[18] == 0x1b8;
      var s20 := Dup(s19, 4);
      assert s20.stack[19] == 0x1b8;
      var s21 := Dup(s20, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s233(s21, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 116
    * Starting at 0xa9d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[20] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[20] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[21] == 0x1b8;
      var s3 := Dup(s2, 4);
      assert s3.stack[22] == 0x1b8;
      var s4 := Lt(s3);
      assert s4.stack[21] == 0x1b8;
      var s5 := PushN(s4, 2, 0x0ada);
      assert s5.stack[0] == 0xada;
      assert s5.stack[22] == 0x1b8;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s235(s6, gas - 1)
      else
        ExecuteFromCFGNode_s234(s6, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 117
    * Starting at 0xaa6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[20] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[21] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[21] == 0x1b8;
      var s3 := Dup(s2, 3);
      assert s3.stack[22] == 0x1b8;
      var s4 := MStore(s3);
      assert s4.stack[20] == 0x1b8;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[21] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[21] == 0x1b8;
      var s7 := Swap(s6, 3);
      assert s7.stack[21] == 0x1b8;
      var s8 := Add(s7);
      assert s8.stack[20] == 0x1b8;
      var s9 := Swap(s8, 2);
      assert s9.stack[20] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[21] == 0x1b8;
      var s11 := Swap(s10, 2);
      assert s11.stack[21] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[22] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[21] == 0x1b8;
      var s14 := Swap(s13, 2);
      assert s14.stack[21] == 0x1b8;
      var s15 := Add(s14);
      assert s15.stack[20] == 0x1b8;
      var s16 := PushN(s15, 2, 0x0a9d);
      assert s16.stack[0] == 0xa9d;
      assert s16.stack[21] == 0x1b8;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s17, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 118
    * Starting at 0xada
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xada as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[20] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[20] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[20] == 0x1b8;
      var s3 := Dup(s2, 2);
      assert s3.stack[21] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[21] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[22] == 0x1b8;
      var s6 := Swap(s5, 4);
      assert s6.stack[22] == 0x1b8;
      var s7 := Dup(s6, 5);
      assert s7.stack[23] == 0x1b8;
      var s8 := Sub(s7);
      assert s8.stack[22] == 0x1b8;
      var s9 := PushN(s8, 2, 0x0100);
      assert s9.stack[23] == 0x1b8;
      var s10 := Exp(s9);
      assert s10.stack[22] == 0x1b8;
      var s11 := PushN(s10, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s11.stack[23] == 0x1b8;
      var s12 := Add(s11);
      assert s12.stack[22] == 0x1b8;
      var s13 := Dup(s12, 1);
      assert s13.stack[23] == 0x1b8;
      var s14 := Not(s13);
      assert s14.stack[23] == 0x1b8;
      var s15 := Swap(s14, 1);
      assert s15.stack[23] == 0x1b8;
      var s16 := Swap(s15, 3);
      assert s16.stack[23] == 0x1b8;
      var s17 := And(s16);
      assert s17.stack[22] == 0x1b8;
      var s18 := Swap(s17, 2);
      assert s18.stack[22] == 0x1b8;
      var s19 := And(s18);
      assert s19.stack[21] == 0x1b8;
      var s20 := Or(s19);
      assert s20.stack[20] == 0x1b8;
      var s21 := Swap(s20, 1);
      assert s21.stack[20] == 0x1b8;
      var s22 := MStore(s21);
      assert s22.stack[18] == 0x1b8;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[19] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[19] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[19] == 0x1b8;
      var s26 := Swap(s25, 1);
      assert s26.stack[19] == 0x1b8;
      var s27 := Swap(s26, 4);
      assert s27.stack[19] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[18] == 0x1b8;
      var s29 := Swap(s28, 5);
      assert s29.stack[18] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[17] == 0x1b8;
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s236(s31, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 119
    * Starting at 0xb1d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[17] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[17] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[16] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[15] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[16] == 0x1b8;
      var s5 := Dup(s4, 4);
      assert s5.stack[17] == 0x1b8;
      var s6 := Sub(s5);
      assert s6.stack[16] == 0x1b8;
      var s7 := Dup(s6, 2);
      assert s7.stack[17] == 0x1b8;
      var s8 := Dup(s7, 6);
      assert s8.stack[18] == 0x1b8;
      var s9 := Gas(s8);
      assert s9.stack[19] == 0x1b8;
      var s10 := StaticCall(s9);
      assert s10.stack[14] == 0x1b8;
      var s11 := IsZero(s10);
      assert s11.stack[14] == 0x1b8;
      var s12 := Dup(s11, 1);
      assert s12.stack[15] == 0x1b8;
      var s13 := IsZero(s12);
      assert s13.stack[15] == 0x1b8;
      var s14 := PushN(s13, 2, 0x0b37);
      assert s14.stack[0] == 0xb37;
      assert s14.stack[16] == 0x1b8;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s238(s15, gas - 1)
      else
        ExecuteFromCFGNode_s237(s15, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 120
    * Starting at 0xb2e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.stack[15] == 0x1b8;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[16] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[17] == 0x1b8;
      var s4 := ReturnDataCopy(s3);
      assert s4.stack[14] == 0x1b8;
      var s5 := ReturnDataSize(s4);
      assert s5.stack[15] == 0x1b8;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[16] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 238
    * Segment Id for this node is: 121
    * Starting at 0xb37
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[14] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[13] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[12] == 0x1b8;
      var s4 := Pop(s3);
      assert s4.stack[11] == 0x1b8;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[12] == 0x1b8;
      var s6 := MLoad(s5);
      assert s6.stack[12] == 0x1b8;
      var s7 := ReturnDataSize(s6);
      assert s7.stack[13] == 0x1b8;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[14] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[15] == 0x1b8;
      var s10 := Lt(s9);
      assert s10.stack[14] == 0x1b8;
      var s11 := IsZero(s10);
      assert s11.stack[14] == 0x1b8;
      var s12 := PushN(s11, 2, 0x0b4c);
      assert s12.stack[0] == 0xb4c;
      assert s12.stack[15] == 0x1b8;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s13, gas - 1)
      else
        ExecuteFromCFGNode_s239(s13, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 122
    * Starting at 0xb48
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[14] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[15] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 240
    * Segment Id for this node is: 123
    * Starting at 0xb4c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[13] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[12] == 0x1b8;
      var s3 := MLoad(s2);
      assert s3.stack[12] == 0x1b8;
      var s4 := PushN(s3, 1, 0x40);
      assert s4.stack[13] == 0x1b8;
      var s5 := Dup(s4, 1);
      assert s5.stack[14] == 0x1b8;
      var s6 := MLoad(s5);
      assert s6.stack[14] == 0x1b8;
      var s7 := PushN(s6, 1, 0x20);
      assert s7.stack[15] == 0x1b8;
      var s8 := Dup(s7, 2);
      assert s8.stack[16] == 0x1b8;
      var s9 := Add(s8);
      assert s9.stack[15] == 0x1b8;
      var s10 := Dup(s9, 6);
      assert s10.stack[16] == 0x1b8;
      var s11 := Dup(s10, 2);
      assert s11.stack[17] == 0x1b8;
      var s12 := MStore(s11);
      assert s12.stack[15] == 0x1b8;
      var s13 := Swap(s12, 3);
      assert s13.stack[15] == 0x1b8;
      var s14 := Swap(s13, 4);
      assert s14.stack[15] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[14] == 0x1b8;
      var s16 := PushN(s15, 1, 0x00);
      assert s16.stack[15] == 0x1b8;
      var s17 := Swap(s16, 3);
      assert s17.stack[15] == 0x1b8;
      var s18 := PushN(s17, 1, 0x02);
      assert s18.stack[16] == 0x1b8;
      var s19 := Swap(s18, 3);
      assert s19.stack[16] == 0x1b8;
      var s20 := Dup(s19, 4);
      assert s20.stack[17] == 0x1b8;
      var s21 := Swap(s20, 3);
      assert s21.stack[17] == 0x1b8;
      var s22 := Dup(s21, 8);
      assert s22.stack[18] == 0x1b8;
      var s23 := Swap(s22, 3);
      assert s23.stack[18] == 0x1b8;
      var s24 := Dup(s23, 16);
      assert s24.stack[19] == 0x1b8;
      var s25 := Swap(s24, 3);
      assert s25.stack[19] == 0x1b8;
      var s26 := Dup(s25, 16);
      assert s26.stack[20] == 0x1b8;
      var s27 := Swap(s26, 3);
      assert s27.stack[20] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[19] == 0x1b8;
      var s29 := Dup(s28, 4);
      assert s29.stack[20] == 0x1b8;
      var s30 := Dup(s29, 4);
      assert s30.stack[21] == 0x1b8;
      var s31 := Dup(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s241(s31, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 124
    * Starting at 0xb6f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[22] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[23] == 0x1b8;
      var s2 := Dup(s1, 5);
      assert s2.stack[24] == 0x1b8;
      var s3 := CallDataCopy(s2);
      assert s3.stack[21] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[22] == 0x1b8;
      var s5 := Dup(s4, 4);
      assert s5.stack[23] == 0x1b8;
      var s6 := Add(s5);
      assert s6.stack[22] == 0x1b8;
      var s7 := Swap(s6, 3);
      assert s7.stack[22] == 0x1b8;
      var s8 := Pop(s7);
      assert s8.stack[21] == 0x1b8;
      var s9 := Pop(s8);
      assert s9.stack[20] == 0x1b8;
      var s10 := Pop(s9);
      assert s10.stack[19] == 0x1b8;
      var s11 := Swap(s10, 4);
      assert s11.stack[19] == 0x1b8;
      var s12 := Pop(s11);
      assert s12.stack[18] == 0x1b8;
      var s13 := Pop(s12);
      assert s13.stack[17] == 0x1b8;
      var s14 := Pop(s13);
      assert s14.stack[16] == 0x1b8;
      var s15 := Pop(s14);
      assert s15.stack[15] == 0x1b8;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[16] == 0x1b8;
      var s17 := MLoad(s16);
      assert s17.stack[16] == 0x1b8;
      var s18 := PushN(s17, 1, 0x20);
      assert s18.stack[17] == 0x1b8;
      var s19 := Dup(s18, 2);
      assert s19.stack[18] == 0x1b8;
      var s20 := Dup(s19, 4);
      assert s20.stack[19] == 0x1b8;
      var s21 := Sub(s20);
      assert s21.stack[18] == 0x1b8;
      var s22 := Sub(s21);
      assert s22.stack[17] == 0x1b8;
      var s23 := Dup(s22, 2);
      assert s23.stack[18] == 0x1b8;
      var s24 := MStore(s23);
      assert s24.stack[16] == 0x1b8;
      var s25 := Swap(s24, 1);
      assert s25.stack[16] == 0x1b8;
      var s26 := PushN(s25, 1, 0x40);
      assert s26.stack[17] == 0x1b8;
      var s27 := MStore(s26);
      assert s27.stack[15] == 0x1b8;
      var s28 := PushN(s27, 1, 0x40);
      assert s28.stack[16] == 0x1b8;
      var s29 := MLoad(s28);
      assert s29.stack[16] == 0x1b8;
      var s30 := Dup(s29, 1);
      assert s30.stack[17] == 0x1b8;
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s242(s31, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 125
    * Starting at 0xb92
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[18] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[19] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[19] == 0x1b8;
      var s3 := Swap(s2, 1);
      assert s3.stack[19] == 0x1b8;
      var s4 := PushN(s3, 1, 0x20);
      assert s4.stack[20] == 0x1b8;
      var s5 := Add(s4);
      assert s5.stack[19] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[19] == 0x1b8;
      var s7 := Dup(s6, 1);
      assert s7.stack[20] == 0x1b8;
      var s8 := Dup(s7, 4);
      assert s8.stack[21] == 0x1b8;
      var s9 := Dup(s8, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s243(s9, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 126
    * Starting at 0xb9c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[22] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[22] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[23] == 0x1b8;
      var s3 := Dup(s2, 4);
      assert s3.stack[24] == 0x1b8;
      var s4 := Lt(s3);
      assert s4.stack[23] == 0x1b8;
      var s5 := PushN(s4, 2, 0x0bd9);
      assert s5.stack[0] == 0xbd9;
      assert s5.stack[24] == 0x1b8;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s245(s6, gas - 1)
      else
        ExecuteFromCFGNode_s244(s6, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 127
    * Starting at 0xba5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[22] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[23] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[23] == 0x1b8;
      var s3 := Dup(s2, 3);
      assert s3.stack[24] == 0x1b8;
      var s4 := MStore(s3);
      assert s4.stack[22] == 0x1b8;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[23] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[23] == 0x1b8;
      var s7 := Swap(s6, 3);
      assert s7.stack[23] == 0x1b8;
      var s8 := Add(s7);
      assert s8.stack[22] == 0x1b8;
      var s9 := Swap(s8, 2);
      assert s9.stack[22] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[23] == 0x1b8;
      var s11 := Swap(s10, 2);
      assert s11.stack[23] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[24] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[23] == 0x1b8;
      var s14 := Swap(s13, 2);
      assert s14.stack[23] == 0x1b8;
      var s15 := Add(s14);
      assert s15.stack[22] == 0x1b8;
      var s16 := PushN(s15, 2, 0x0b9c);
      assert s16.stack[0] == 0xb9c;
      assert s16.stack[23] == 0x1b8;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s17, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 128
    * Starting at 0xbd9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[22] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[22] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[22] == 0x1b8;
      var s3 := Dup(s2, 2);
      assert s3.stack[23] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[23] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[24] == 0x1b8;
      var s6 := Swap(s5, 4);
      assert s6.stack[24] == 0x1b8;
      var s7 := Dup(s6, 5);
      assert s7.stack[25] == 0x1b8;
      var s8 := Sub(s7);
      assert s8.stack[24] == 0x1b8;
      var s9 := PushN(s8, 2, 0x0100);
      assert s9.stack[25] == 0x1b8;
      var s10 := Exp(s9);
      assert s10.stack[24] == 0x1b8;
      var s11 := PushN(s10, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s11.stack[25] == 0x1b8;
      var s12 := Add(s11);
      assert s12.stack[24] == 0x1b8;
      var s13 := Dup(s12, 1);
      assert s13.stack[25] == 0x1b8;
      var s14 := Not(s13);
      assert s14.stack[25] == 0x1b8;
      var s15 := Swap(s14, 1);
      assert s15.stack[25] == 0x1b8;
      var s16 := Swap(s15, 3);
      assert s16.stack[25] == 0x1b8;
      var s17 := And(s16);
      assert s17.stack[24] == 0x1b8;
      var s18 := Swap(s17, 2);
      assert s18.stack[24] == 0x1b8;
      var s19 := And(s18);
      assert s19.stack[23] == 0x1b8;
      var s20 := Or(s19);
      assert s20.stack[22] == 0x1b8;
      var s21 := Swap(s20, 1);
      assert s21.stack[22] == 0x1b8;
      var s22 := MStore(s21);
      assert s22.stack[20] == 0x1b8;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[21] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[21] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[21] == 0x1b8;
      var s26 := Swap(s25, 1);
      assert s26.stack[21] == 0x1b8;
      var s27 := Swap(s26, 4);
      assert s27.stack[21] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[20] == 0x1b8;
      var s29 := Swap(s28, 5);
      assert s29.stack[20] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[19] == 0x1b8;
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s246(s31, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 129
    * Starting at 0xc1c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[19] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[19] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[18] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[17] == 0x1b8;
      var s4 := Dup(s3, 1);
      assert s4.stack[18] == 0x1b8;
      var s5 := Dup(s4, 4);
      assert s5.stack[19] == 0x1b8;
      var s6 := Sub(s5);
      assert s6.stack[18] == 0x1b8;
      var s7 := Dup(s6, 2);
      assert s7.stack[19] == 0x1b8;
      var s8 := Dup(s7, 6);
      assert s8.stack[20] == 0x1b8;
      var s9 := Gas(s8);
      assert s9.stack[21] == 0x1b8;
      var s10 := StaticCall(s9);
      assert s10.stack[16] == 0x1b8;
      var s11 := IsZero(s10);
      assert s11.stack[16] == 0x1b8;
      var s12 := Dup(s11, 1);
      assert s12.stack[17] == 0x1b8;
      var s13 := IsZero(s12);
      assert s13.stack[17] == 0x1b8;
      var s14 := PushN(s13, 2, 0x0c36);
      assert s14.stack[0] == 0xc36;
      assert s14.stack[18] == 0x1b8;
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s15, gas - 1)
      else
        ExecuteFromCFGNode_s247(s15, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 130
    * Starting at 0xc2d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.stack[17] == 0x1b8;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[18] == 0x1b8;
      var s3 := Dup(s2, 1);
      assert s3.stack[19] == 0x1b8;
      var s4 := ReturnDataCopy(s3);
      assert s4.stack[16] == 0x1b8;
      var s5 := ReturnDataSize(s4);
      assert s5.stack[17] == 0x1b8;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[18] == 0x1b8;
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 248
    * Segment Id for this node is: 131
    * Starting at 0xc36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[16] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[16] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[15] == 0x1b8;
      var s3 := Pop(s2);
      assert s3.stack[14] == 0x1b8;
      var s4 := Pop(s3);
      assert s4.stack[13] == 0x1b8;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[14] == 0x1b8;
      var s6 := MLoad(s5);
      assert s6.stack[14] == 0x1b8;
      var s7 := ReturnDataSize(s6);
      assert s7.stack[15] == 0x1b8;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[16] == 0x1b8;
      var s9 := Dup(s8, 2);
      assert s9.stack[17] == 0x1b8;
      var s10 := Lt(s9);
      assert s10.stack[16] == 0x1b8;
      var s11 := IsZero(s10);
      assert s11.stack[16] == 0x1b8;
      var s12 := PushN(s11, 2, 0x0c4b);
      assert s12.stack[0] == 0xc4b;
      assert s12.stack[17] == 0x1b8;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s250(s13, gas - 1)
      else
        ExecuteFromCFGNode_s249(s13, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 132
    * Starting at 0xc47
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc47 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[16] == 0x1b8;
      var s2 := Dup(s1, 1);
      assert s2.stack[17] == 0x1b8;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 250
    * Segment Id for this node is: 133
    * Starting at 0xc4b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[15] == 0x1b8;
      var s2 := Pop(s1);
      assert s2.stack[14] == 0x1b8;
      var s3 := MLoad(s2);
      assert s3.stack[14] == 0x1b8;
      var s4 := PushN(s3, 1, 0x40);
      assert s4.stack[15] == 0x1b8;
      var s5 := MLoad(s4);
      assert s5.stack[15] == 0x1b8;
      var s6 := Dup(s5, 7);
      assert s6.stack[16] == 0x1b8;
      var s7 := MLoad(s6);
      assert s7.stack[16] == 0x1b8;
      var s8 := PushN(s7, 1, 0x02);
      assert s8.stack[17] == 0x1b8;
      var s9 := Swap(s8, 2);
      assert s9.stack[17] == 0x1b8;
      var s10 := Dup(s9, 9);
      assert s10.stack[18] == 0x1b8;
      var s11 := Swap(s10, 2);
      assert s11.stack[18] == 0x1b8;
      var s12 := PushN(s11, 1, 0x00);
      assert s12.stack[19] == 0x1b8;
      var s13 := Swap(s12, 2);
      assert s13.stack[19] == 0x1b8;
      var s14 := Dup(s13, 9);
      assert s14.stack[20] == 0x1b8;
      var s15 := Swap(s14, 2);
      assert s15.stack[20] == 0x1b8;
      var s16 := PushN(s15, 1, 0x20);
      assert s16.stack[21] == 0x1b8;
      var s17 := Swap(s16, 2);
      assert s17.stack[21] == 0x1b8;
      var s18 := Dup(s17, 3);
      assert s18.stack[22] == 0x1b8;
      var s19 := Add(s18);
      assert s19.stack[21] == 0x1b8;
      var s20 := Swap(s19, 2);
      assert s20.stack[21] == 0x1b8;
      var s21 := Dup(s20, 3);
      assert s21.stack[22] == 0x1b8;
      var s22 := Swap(s21, 2);
      assert s22.stack[22] == 0x1b8;
      var s23 := Swap(s22, 1);
      assert s23.stack[22] == 0x1b8;
      var s24 := Dup(s23, 7);
      assert s24.stack[23] == 0x1b8;
      var s25 := Add(s24);
      assert s25.stack[22] == 0x1b8;
      var s26 := Swap(s25, 1);
      assert s26.stack[22] == 0x1b8;
      var s27 := Dup(s26, 1);
      assert s27.stack[23] == 0x1b8;
      var s28 := Dup(s27, 4);
      assert s28.stack[24] == 0x1b8;
      var s29 := Dup(s28, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s251(s29, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 134
    * Starting at 0xc6c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[25] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[25] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[26] == 0x1b8;
      var s3 := Dup(s2, 4);
      assert s3.stack[27] == 0x1b8;
      var s4 := Lt(s3);
      assert s4.stack[26] == 0x1b8;
      var s5 := PushN(s4, 2, 0x0ca9);
      assert s5.stack[0] == 0xca9;
      assert s5.stack[27] == 0x1b8;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s253(s6, gas - 1)
      else
        ExecuteFromCFGNode_s252(s6, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 135
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[25] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[26] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[26] == 0x1b8;
      var s3 := Dup(s2, 3);
      assert s3.stack[27] == 0x1b8;
      var s4 := MStore(s3);
      assert s4.stack[25] == 0x1b8;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[26] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[26] == 0x1b8;
      var s7 := Swap(s6, 3);
      assert s7.stack[26] == 0x1b8;
      var s8 := Add(s7);
      assert s8.stack[25] == 0x1b8;
      var s9 := Swap(s8, 2);
      assert s9.stack[25] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[26] == 0x1b8;
      var s11 := Swap(s10, 2);
      assert s11.stack[26] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[27] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[26] == 0x1b8;
      var s14 := Swap(s13, 2);
      assert s14.stack[26] == 0x1b8;
      var s15 := Add(s14);
      assert s15.stack[25] == 0x1b8;
      var s16 := PushN(s15, 2, 0x0c6c);
      assert s16.stack[0] == 0xc6c;
      assert s16.stack[26] == 0x1b8;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s17, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 136
    * Starting at 0xca9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[25] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[25] == 0x1b8;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[26] == 0x1b8;
      var s3 := Dup(s2, 4);
      assert s3.stack[27] == 0x1b8;
      var s4 := PushN(s3, 1, 0x20);
      assert s4.stack[28] == 0x1b8;
      var s5 := Sub(s4);
      assert s5.stack[27] == 0x1b8;
      var s6 := PushN(s5, 2, 0x0100);
      assert s6.stack[28] == 0x1b8;
      var s7 := Exp(s6);
      assert s7.stack[27] == 0x1b8;
      var s8 := Sub(s7);
      assert s8.stack[26] == 0x1b8;
      var s9 := Dup(s8, 1);
      assert s9.stack[27] == 0x1b8;
      var s10 := Not(s9);
      assert s10.stack[27] == 0x1b8;
      var s11 := Dup(s10, 3);
      assert s11.stack[28] == 0x1b8;
      var s12 := MLoad(s11);
      assert s12.stack[28] == 0x1b8;
      var s13 := And(s12);
      assert s13.stack[27] == 0x1b8;
      var s14 := Dup(s13, 2);
      assert s14.stack[28] == 0x1b8;
      var s15 := Dup(s14, 5);
      assert s15.stack[29] == 0x1b8;
      var s16 := MLoad(s15);
      assert s16.stack[29] == 0x1b8;
      var s17 := And(s16);
      assert s17.stack[28] == 0x1b8;
      var s18 := Dup(s17, 1);
      assert s18.stack[29] == 0x1b8;
      var s19 := Dup(s18, 3);
      assert s19.stack[30] == 0x1b8;
      var s20 := Or(s19);
      assert s20.stack[29] == 0x1b8;
      var s21 := Dup(s20, 6);
      assert s21.stack[30] == 0x1b8;
      var s22 := MStore(s21);
      assert s22.stack[28] == 0x1b8;
      var s23 := Pop(s22);
      assert s23.stack[27] == 0x1b8;
      var s24 := Pop(s23);
      assert s24.stack[26] == 0x1b8;
      var s25 := Pop(s24);
      assert s25.stack[25] == 0x1b8;
      var s26 := Pop(s25);
      assert s26.stack[24] == 0x1b8;
      var s27 := Pop(s26);
      assert s27.stack[23] == 0x1b8;
      var s28 := Pop(s27);
      assert s28.stack[22] == 0x1b8;
      var s29 := Swap(s28, 1);
      assert s29.stack[22] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[21] == 0x1b8;
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s254(s31, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 137
    * Starting at 0xccc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[20] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 4);
      assert s1.stack[21] == 0x1b8;
      var s2 := PushN(s1, 8, 0xffffffffffffffff);
      assert s2.stack[22] == 0x1b8;
      var s3 := Not(s2);
      assert s3.stack[22] == 0x1b8;
      var s4 := And(s3);
      assert s4.stack[21] == 0x1b8;
      var s5 := PushN(s4, 8, 0xffffffffffffffff);
      assert s5.stack[22] == 0x1b8;
      var s6 := Not(s5);
      assert s6.stack[22] == 0x1b8;
      var s7 := And(s6);
      assert s7.stack[21] == 0x1b8;
      var s8 := Dup(s7, 2);
      assert s8.stack[22] == 0x1b8;
      var s9 := MStore(s8);
      assert s9.stack[20] == 0x1b8;
      var s10 := PushN(s9, 1, 0x18);
      assert s10.stack[21] == 0x1b8;
      var s11 := Add(s10);
      assert s11.stack[20] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[21] == 0x1b8;
      var s13 := Dup(s12, 2);
      assert s13.stack[22] == 0x1b8;
      var s14 := MStore(s13);
      assert s14.stack[20] == 0x1b8;
      var s15 := PushN(s14, 1, 0x20);
      assert s15.stack[21] == 0x1b8;
      var s16 := Add(s15);
      assert s16.stack[20] == 0x1b8;
      var s17 := Swap(s16, 4);
      assert s17.stack[20] == 0x1b8;
      var s18 := Pop(s17);
      assert s18.stack[19] == 0x1b8;
      var s19 := Pop(s18);
      assert s19.stack[18] == 0x1b8;
      var s20 := Pop(s19);
      assert s20.stack[17] == 0x1b8;
      var s21 := Pop(s20);
      assert s21.stack[16] == 0x1b8;
      var s22 := PushN(s21, 1, 0x40);
      assert s22.stack[17] == 0x1b8;
      var s23 := MLoad(s22);
      assert s23.stack[17] == 0x1b8;
      var s24 := PushN(s23, 1, 0x20);
      assert s24.stack[18] == 0x1b8;
      var s25 := Dup(s24, 2);
      assert s25.stack[19] == 0x1b8;
      var s26 := Dup(s25, 4);
      assert s26.stack[20] == 0x1b8;
      var s27 := Sub(s26);
      assert s27.stack[19] == 0x1b8;
      var s28 := Sub(s27);
      assert s28.stack[18] == 0x1b8;
      var s29 := Dup(s28, 2);
      assert s29.stack[19] == 0x1b8;
      var s30 := MStore(s29);
      assert s30.stack[17] == 0x1b8;
      var s31 := Swap(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s255(s31, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 138
    * Starting at 0xcff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[17] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[18] == 0x1b8;
      var s2 := MStore(s1);
      assert s2.stack[16] == 0x1b8;
      var s3 := PushN(s2, 1, 0x40);
      assert s3.stack[17] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[17] == 0x1b8;
      var s5 := Dup(s4, 1);
      assert s5.stack[18] == 0x1b8;
      var s6 := Dup(s5, 3);
      assert s6.stack[19] == 0x1b8;
      var s7 := Dup(s6, 1);
      assert s7.stack[20] == 0x1b8;
      var s8 := MLoad(s7);
      assert s8.stack[20] == 0x1b8;
      var s9 := Swap(s8, 1);
      assert s9.stack[20] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[21] == 0x1b8;
      var s11 := Add(s10);
      assert s11.stack[20] == 0x1b8;
      var s12 := Swap(s11, 1);
      assert s12.stack[20] == 0x1b8;
      var s13 := Dup(s12, 1);
      assert s13.stack[21] == 0x1b8;
      var s14 := Dup(s13, 4);
      assert s14.stack[22] == 0x1b8;
      var s15 := Dup(s14, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s256(s15, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 139
    * Starting at 0xd11
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[23] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[23] == 0x1b8;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[24] == 0x1b8;
      var s3 := Dup(s2, 4);
      assert s3.stack[25] == 0x1b8;
      var s4 := Lt(s3);
      assert s4.stack[24] == 0x1b8;
      var s5 := PushN(s4, 2, 0x0d4e);
      assert s5.stack[0] == 0xd4e;
      assert s5.stack[25] == 0x1b8;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s258(s6, gas - 1)
      else
        ExecuteFromCFGNode_s257(s6, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 140
    * Starting at 0xd1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[23] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[24] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[24] == 0x1b8;
      var s3 := Dup(s2, 3);
      assert s3.stack[25] == 0x1b8;
      var s4 := MStore(s3);
      assert s4.stack[23] == 0x1b8;
      var s5 := PushN(s4, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s5.stack[24] == 0x1b8;
      var s6 := Swap(s5, 1);
      assert s6.stack[24] == 0x1b8;
      var s7 := Swap(s6, 3);
      assert s7.stack[24] == 0x1b8;
      var s8 := Add(s7);
      assert s8.stack[23] == 0x1b8;
      var s9 := Swap(s8, 2);
      assert s9.stack[23] == 0x1b8;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[24] == 0x1b8;
      var s11 := Swap(s10, 2);
      assert s11.stack[24] == 0x1b8;
      var s12 := Dup(s11, 3);
      assert s12.stack[25] == 0x1b8;
      var s13 := Add(s12);
      assert s13.stack[24] == 0x1b8;
      var s14 := Swap(s13, 2);
      assert s14.stack[24] == 0x1b8;
      var s15 := Add(s14);
      assert s15.stack[23] == 0x1b8;
      var s16 := PushN(s15, 2, 0x0d11);
      assert s16.stack[0] == 0xd11;
      assert s16.stack[24] == 0x1b8;
      var s17 := Jump(s16);
      // Segment is terminal (Revert, Stop or Return)
      s17
  }

  /** Node 258
    * Segment Id for this node is: 141
    * Starting at 0xd4e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[23] == 0x1b8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[23] == 0x1b8;
      var s2 := MLoad(s1);
      assert s2.stack[23] == 0x1b8;
      var s3 := Dup(s2, 2);
      assert s3.stack[24] == 0x1b8;
      var s4 := MLoad(s3);
      assert s4.stack[24] == 0x1b8;
      var s5 := PushN(s4, 1, 0x20);
      assert s5.stack[25] == 0x1b8;
      var s6 := Swap(s5, 4);
      assert s6.stack[25] == 0x1b8;
      var s7 := Dup(s6, 5);
      assert s7.stack[26] == 0x1b8;
      var s8 := Sub(s7);
      assert s8.stack[25] == 0x1b8;
      var s9 := PushN(s8, 2, 0x0100);
      assert s9.stack[26] == 0x1b8;
      var s10 := Exp(s9);
      assert s10.stack[25] == 0x1b8;
      var s11 := PushN(s10, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s11.stack[26] == 0x1b8;
      var s12 := Add(s11);
      assert s12.stack[25] == 0x1b8;
      var s13 := Dup(s12, 1);
      assert s13.stack[26] == 0x1b8;
      var s14 := Not(s13);
      assert s14.stack[26] == 0x1b8;
      var s15 := Swap(s14, 1);
      assert s15.stack[26] == 0x1b8;
      var s16 := Swap(s15, 3);
      assert s16.stack[26] == 0x1b8;
      var s17 := And(s16);
      assert s17.stack[25] == 0x1b8;
      var s18 := Swap(s17, 2);
      assert s18.stack[25] == 0x1b8;
      var s19 := And(s18);
      assert s19.stack[24] == 0x1b8;
      var s20 := Or(s19);
      assert s20.stack[23] == 0x1b8;
      var s21 := Swap(s20, 1);
      assert s21.stack[23] == 0x1b8;
      var s22 := MStore(s21);
      assert s22.stack[21] == 0x1b8;
      var s23 := PushN(s22, 1, 0x40);
      assert s23.stack[22] == 0x1b8;
      var s24 := MLoad(s23);
      assert s24.stack[22] == 0x1b8;
      var s25 := Swap(s24, 2);
      assert s25.stack[22] == 0x1b8;
      var s26 := Swap(s25, 1);
      assert s26.stack[22] == 0x1b8;
      var s27 := Swap(s26, 4);
      assert s27.stack[22] == 0x1b8;
      var s28 := Add(s27);
      assert s28.stack[21] == 0x1b8;
      var s29 := Swap(s28, 5);
      assert s29.stack[21] == 0x1b8;
      var s30 := Pop(s29);
      assert s30.stack[20] == 0x1b8;
      var s31 := Swap(s30, 2);
      // Segment is terminal (Revert, Stop or Return)
      s31
  }

  /** Node 259
    * Segment Id for this node is: 6
    * Starting at 0x44
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup(s2, 1);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x0050);
      assert s5.stack[0] == 0x50;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s261(s6, gas - 1)
      else
        ExecuteFromCFGNode_s260(s6, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 7
    * Starting at 0x4c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := Dup(s1, 1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 261
    * Segment Id for this node is: 8
    * Starting at 0x50
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 2, 0x0090);
      assert s3.stack[0] == 0x90;
      var s4 := PushN(s3, 1, 0x04);
      assert s4.stack[1] == 0x90;
      var s5 := Dup(s4, 1);
      assert s5.stack[2] == 0x90;
      var s6 := CallDataSize(s5);
      assert s6.stack[3] == 0x90;
      var s7 := Sub(s6);
      assert s7.stack[2] == 0x90;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[3] == 0x90;
      var s9 := Dup(s8, 2);
      assert s9.stack[4] == 0x90;
      var s10 := Lt(s9);
      assert s10.stack[3] == 0x90;
      var s11 := IsZero(s10);
      assert s11.stack[3] == 0x90;
      var s12 := PushN(s11, 2, 0x0067);
      assert s12.stack[0] == 0x67;
      assert s12.stack[4] == 0x90;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s13, gas - 1)
      else
        ExecuteFromCFGNode_s262(s13, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 9
    * Starting at 0x63
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[3] == 0x90;
      var s2 := Dup(s1, 1);
      assert s2.stack[4] == 0x90;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 263
    * Segment Id for this node is: 10
    * Starting at 0x67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x90;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x90;
      var s3 := CallDataLoad(s2);
      assert s3.stack[1] == 0x90;
      var s4 := PushN(s3, 32, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      assert s4.stack[2] == 0x90;
      var s5 := And(s4);
      assert s5.stack[1] == 0x90;
      var s6 := PushN(s5, 2, 0x026b);
      assert s6.stack[0] == 0x26b;
      assert s6.stack[2] == 0x90;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s7, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 47
    * Starting at 0x26b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x90;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[2] == 0x90;
      var s3 := PushN(s2, 32, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      assert s3.stack[3] == 0x90;
      var s4 := Dup(s3, 3);
      assert s4.stack[4] == 0x90;
      var s5 := And(s4);
      assert s5.stack[3] == 0x90;
      var s6 := PushN(s5, 32, 0x01ffc9a700000000000000000000000000000000000000000000000000000000);
      assert s6.stack[4] == 0x90;
      var s7 := Eq(s6);
      assert s7.stack[3] == 0x90;
      var s8 := Dup(s7, 1);
      assert s8.stack[4] == 0x90;
      var s9 := PushN(s8, 2, 0x02fe);
      assert s9.stack[0] == 0x2fe;
      assert s9.stack[5] == 0x90;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s266(s10, gas - 1)
      else
        ExecuteFromCFGNode_s265(s10, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 48
    * Starting at 0x2b8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[2] == 0x90;
      var s2 := PushN(s1, 32, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      assert s2.stack[3] == 0x90;
      var s3 := Dup(s2, 3);
      assert s3.stack[4] == 0x90;
      var s4 := And(s3);
      assert s4.stack[3] == 0x90;
      var s5 := PushN(s4, 32, 0x8564090700000000000000000000000000000000000000000000000000000000);
      assert s5.stack[4] == 0x90;
      var s6 := Eq(s5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s266(s6, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 49
    * Starting at 0x2fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x90;
      var s2 := Swap(s1, 3);
      assert s2.stack[0] == 0x90;
      var s3 := Swap(s2, 2);
      assert s3.stack[2] == 0x90;
      var s4 := Pop(s3);
      assert s4.stack[1] == 0x90;
      var s5 := Pop(s4);
      assert s5.stack[0] == 0x90;
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s267(s6, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 11
    * Starting at 0x90
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := Dup(s2, 1);
      var s4 := MLoad(s3);
      var s5 := Swap(s4, 2);
      var s6 := IsZero(s5);
      var s7 := IsZero(s6);
      var s8 := Dup(s7, 3);
      var s9 := MStore(s8);
      var s10 := MLoad(s9);
      var s11 := Swap(s10, 1);
      var s12 := Dup(s11, 2);
      var s13 := Swap(s12, 1);
      var s14 := Sub(s13);
      var s15 := PushN(s14, 1, 0x20);
      var s16 := Add(s15);
      var s17 := Swap(s16, 1);
      var s18 := Return(s17);
      // Segment is terminal (Revert, Stop or Return)
      s18
  }

  /** Node 268
    * Segment Id for this node is: 5
    * Starting at 0x3f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

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
}
