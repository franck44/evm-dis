
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
      var s1 := PushN(s0, 1, 0x60);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 1, 0x04);
      var s5 := CallDataSize(s4);
      var s6 := Lt(s5);
      var s7 := PushN(s6, 2, 0x00af);
      assert s7.stack[0] == 0xaf;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s135(s8, gas - 1)
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
      var s3 := PushN(s2, 29, 0x0100000000000000000000000000000000000000000000000000000000);
      var s4 := Swap(s3, 1);
      var s5 := Div(s4);
      var s6 := PushN(s5, 4, 0xffffffff);
      var s7 := And(s6);
      var s8 := Dup(s7, 1);
      var s9 := PushN(s8, 4, 0x06fdde03);
      var s10 := Eq(s9);
      var s11 := PushN(s10, 2, 0x00b9);
      assert s11.stack[0] == 0xb9;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s117(s12, gas - 1)
      else
        ExecuteFromCFGNode_s2(s12, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x0147);
      assert s4.stack[0] == 0x147;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s5, gas - 1)
      else
        ExecuteFromCFGNode_s3(s5, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x01a1);
      assert s4.stack[0] == 0x1a1;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s5, gas - 1)
      else
        ExecuteFromCFGNode_s4(s5, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x01ca);
      assert s4.stack[0] == 0x1ca;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x62
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x2e1a7d4d);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x0243);
      assert s4.stack[0] == 0x243;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x6d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x0266);
      assert s4.stack[0] == 0x266;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x78
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x0295);
      assert s4.stack[0] == 0x295;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x83
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x02e2);
      assert s4.stack[0] == 0x2e2;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s46(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x8e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x0370);
      assert s4.stack[0] == 0x370;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 10
    * Starting at 0x99
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0xd0e30db0);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x03ca);
      assert s4.stack[0] == 0x3ca;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s5, gas - 1)
      else
        ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 11
    * Starting at 0xa4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x03d4);
      assert s4.stack[0] == 0x3d4;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s5, gas - 1)
      else
        ExecuteFromCFGNode_s12(s5, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 12
    * Starting at 0xaf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x00b7);
      assert s2.stack[0] == 0xb7;
      var s3 := PushN(s2, 2, 0x0440);
      assert s3.stack[0] == 0x440;
      assert s3.stack[1] == 0xb7;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s4, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 69
    * Starting at 0x440
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x440 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0xb7;
      var s2 := CallValue(s1);
      assert s2.stack[1] == 0xb7;
      var s3 := PushN(s2, 1, 0x03);
      assert s3.stack[2] == 0xb7;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[3] == 0xb7;
      var s5 := Caller(s4);
      assert s5.stack[4] == 0xb7;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[5] == 0xb7;
      var s7 := And(s6);
      assert s7.stack[4] == 0xb7;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[5] == 0xb7;
      var s9 := And(s8);
      assert s9.stack[4] == 0xb7;
      var s10 := Dup(s9, 2);
      assert s10.stack[5] == 0xb7;
      var s11 := MStore(s10);
      assert s11.stack[3] == 0xb7;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[4] == 0xb7;
      var s13 := Add(s12);
      assert s13.stack[3] == 0xb7;
      var s14 := Swap(s13, 1);
      assert s14.stack[3] == 0xb7;
      var s15 := Dup(s14, 2);
      assert s15.stack[4] == 0xb7;
      var s16 := MStore(s15);
      assert s16.stack[2] == 0xb7;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[3] == 0xb7;
      var s18 := Add(s17);
      assert s18.stack[2] == 0xb7;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[3] == 0xb7;
      var s20 := Keccak256(s19);
      assert s20.stack[2] == 0xb7;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[3] == 0xb7;
      var s22 := Dup(s21, 3);
      assert s22.stack[4] == 0xb7;
      var s23 := Dup(s22, 3);
      assert s23.stack[5] == 0xb7;
      var s24 := SLoad(s23);
      assert s24.stack[5] == 0xb7;
      var s25 := Add(s24);
      assert s25.stack[4] == 0xb7;
      var s26 := Swap(s25, 3);
      assert s26.stack[4] == 0xb7;
      var s27 := Pop(s26);
      assert s27.stack[3] == 0xb7;
      var s28 := Pop(s27);
      assert s28.stack[2] == 0xb7;
      var s29 := Dup(s28, 2);
      assert s29.stack[3] == 0xb7;
      var s30 := Swap(s29, 1);
      assert s30.stack[3] == 0xb7;
      var s31 := SStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s14(s31, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 70
    * Starting at 0x48d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[0] == 0xb7;
      var s2 := Caller(s1);
      assert s2.stack[1] == 0xb7;
      var s3 := PushN(s2, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s3.stack[2] == 0xb7;
      var s4 := And(s3);
      assert s4.stack[1] == 0xb7;
      var s5 := PushN(s4, 32, 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c);
      assert s5.stack[2] == 0xb7;
      var s6 := CallValue(s5);
      assert s6.stack[3] == 0xb7;
      var s7 := PushN(s6, 1, 0x40);
      assert s7.stack[4] == 0xb7;
      var s8 := MLoad(s7);
      assert s8.stack[4] == 0xb7;
      var s9 := Dup(s8, 1);
      assert s9.stack[5] == 0xb7;
      var s10 := Dup(s9, 3);
      assert s10.stack[6] == 0xb7;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0xb7;
      var s12 := MStore(s11);
      assert s12.stack[5] == 0xb7;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[6] == 0xb7;
      var s14 := Add(s13);
      assert s14.stack[5] == 0xb7;
      var s15 := Swap(s14, 2);
      assert s15.stack[5] == 0xb7;
      var s16 := Pop(s15);
      assert s16.stack[4] == 0xb7;
      var s17 := Pop(s16);
      assert s17.stack[3] == 0xb7;
      var s18 := PushN(s17, 1, 0x40);
      assert s18.stack[4] == 0xb7;
      var s19 := MLoad(s18);
      assert s19.stack[4] == 0xb7;
      var s20 := Dup(s19, 1);
      assert s20.stack[5] == 0xb7;
      var s21 := Swap(s20, 2);
      assert s21.stack[5] == 0xb7;
      var s22 := Sub(s21);
      assert s22.stack[4] == 0xb7;
      var s23 := Swap(s22, 1);
      assert s23.stack[4] == 0xb7;
      var s24 := LogN(s23, 2);
      assert s24.stack[0] == 0xb7;
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s25, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 13
    * Starting at 0xb7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7 as nat
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

  /** Node 16
    * Segment Id for this node is: 65
    * Starting at 0x3d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x03df);
      assert s4.stack[0] == 0x3df;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s18(s5, gas - 1)
      else
        ExecuteFromCFGNode_s17(s5, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 66
    * Starting at 0x3db
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 18
    * Segment Id for this node is: 67
    * Starting at 0x3df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x042a);
      assert s2.stack[0] == 0x42a;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[1] == 0x42a;
      var s4 := Dup(s3, 1);
      assert s4.stack[2] == 0x42a;
      var s5 := Dup(s4, 1);
      assert s5.stack[3] == 0x42a;
      var s6 := CallDataLoad(s5);
      assert s6.stack[3] == 0x42a;
      var s7 := PushN(s6, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s7.stack[4] == 0x42a;
      var s8 := And(s7);
      assert s8.stack[3] == 0x42a;
      var s9 := Swap(s8, 1);
      assert s9.stack[3] == 0x42a;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[4] == 0x42a;
      var s11 := Add(s10);
      assert s11.stack[3] == 0x42a;
      var s12 := Swap(s11, 1);
      assert s12.stack[3] == 0x42a;
      var s13 := Swap(s12, 2);
      assert s13.stack[3] == 0x42a;
      var s14 := Swap(s13, 1);
      assert s14.stack[3] == 0x42a;
      var s15 := Dup(s14, 1);
      assert s15.stack[4] == 0x42a;
      var s16 := CallDataLoad(s15);
      assert s16.stack[4] == 0x42a;
      var s17 := PushN(s16, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s17.stack[5] == 0x42a;
      var s18 := And(s17);
      assert s18.stack[4] == 0x42a;
      var s19 := Swap(s18, 1);
      assert s19.stack[4] == 0x42a;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[5] == 0x42a;
      var s21 := Add(s20);
      assert s21.stack[4] == 0x42a;
      var s22 := Swap(s21, 1);
      assert s22.stack[4] == 0x42a;
      var s23 := Swap(s22, 2);
      assert s23.stack[4] == 0x42a;
      var s24 := Swap(s23, 1);
      assert s24.stack[4] == 0x42a;
      var s25 := Pop(s24);
      assert s25.stack[3] == 0x42a;
      var s26 := Pop(s25);
      assert s26.stack[2] == 0x42a;
      var s27 := PushN(s26, 2, 0x0be3);
      assert s27.stack[0] == 0xbe3;
      assert s27.stack[3] == 0x42a;
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s28, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 117
    * Starting at 0xbe3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x42a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x42a;
      var s2 := PushN(s1, 1, 0x04);
      assert s2.stack[3] == 0x42a;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[4] == 0x42a;
      var s4 := MStore(s3);
      assert s4.stack[2] == 0x42a;
      var s5 := Dup(s4, 2);
      assert s5.stack[3] == 0x42a;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[4] == 0x42a;
      var s7 := MStore(s6);
      assert s7.stack[2] == 0x42a;
      var s8 := PushN(s7, 1, 0x40);
      assert s8.stack[3] == 0x42a;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[4] == 0x42a;
      var s10 := Keccak256(s9);
      assert s10.stack[3] == 0x42a;
      var s11 := PushN(s10, 1, 0x20);
      assert s11.stack[4] == 0x42a;
      var s12 := MStore(s11);
      assert s12.stack[2] == 0x42a;
      var s13 := Dup(s12, 1);
      assert s13.stack[3] == 0x42a;
      var s14 := PushN(s13, 1, 0x00);
      assert s14.stack[4] == 0x42a;
      var s15 := MStore(s14);
      assert s15.stack[2] == 0x42a;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[3] == 0x42a;
      var s17 := PushN(s16, 1, 0x00);
      assert s17.stack[4] == 0x42a;
      var s18 := Keccak256(s17);
      assert s18.stack[3] == 0x42a;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[4] == 0x42a;
      var s20 := Swap(s19, 2);
      assert s20.stack[4] == 0x42a;
      var s21 := Pop(s20);
      assert s21.stack[3] == 0x42a;
      var s22 := Swap(s21, 2);
      assert s22.stack[3] == 0x42a;
      var s23 := Pop(s22);
      assert s23.stack[2] == 0x42a;
      var s24 := Pop(s23);
      assert s24.stack[1] == 0x42a;
      var s25 := SLoad(s24);
      assert s25.stack[1] == 0x42a;
      var s26 := Dup(s25, 2);
      assert s26.stack[0] == 0x42a;
      assert s26.stack[2] == 0x42a;
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s27, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 68
    * Starting at 0x42a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x42a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x42a;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0x42a;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x42a;
      var s4 := Dup(s3, 1);
      assert s4.stack[3] == 0x42a;
      var s5 := Dup(s4, 3);
      assert s5.stack[4] == 0x42a;
      var s6 := Dup(s5, 2);
      assert s6.stack[5] == 0x42a;
      var s7 := MStore(s6);
      assert s7.stack[3] == 0x42a;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[4] == 0x42a;
      var s9 := Add(s8);
      assert s9.stack[3] == 0x42a;
      var s10 := Swap(s9, 2);
      assert s10.stack[3] == 0x42a;
      var s11 := Pop(s10);
      assert s11.stack[2] == 0x42a;
      var s12 := Pop(s11);
      assert s12.stack[1] == 0x42a;
      var s13 := PushN(s12, 1, 0x40);
      assert s13.stack[2] == 0x42a;
      var s14 := MLoad(s13);
      assert s14.stack[2] == 0x42a;
      var s15 := Dup(s14, 1);
      assert s15.stack[3] == 0x42a;
      var s16 := Swap(s15, 2);
      assert s16.stack[3] == 0x42a;
      var s17 := Sub(s16);
      assert s17.stack[2] == 0x42a;
      var s18 := Swap(s17, 1);
      assert s18.stack[2] == 0x42a;
      var s19 := Return(s18);
      // Segment is terminal (Revert, Stop or Return)
      s19
  }

  /** Node 21
    * Segment Id for this node is: 63
    * Starting at 0x3ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x03d2);
      assert s2.stack[0] == 0x3d2;
      var s3 := PushN(s2, 2, 0x0440);
      assert s3.stack[0] == 0x440;
      assert s3.stack[1] == 0x3d2;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s4, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 69
    * Starting at 0x440
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x440 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x3d2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0x3d2;
      var s2 := CallValue(s1);
      assert s2.stack[1] == 0x3d2;
      var s3 := PushN(s2, 1, 0x03);
      assert s3.stack[2] == 0x3d2;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[3] == 0x3d2;
      var s5 := Caller(s4);
      assert s5.stack[4] == 0x3d2;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[5] == 0x3d2;
      var s7 := And(s6);
      assert s7.stack[4] == 0x3d2;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[5] == 0x3d2;
      var s9 := And(s8);
      assert s9.stack[4] == 0x3d2;
      var s10 := Dup(s9, 2);
      assert s10.stack[5] == 0x3d2;
      var s11 := MStore(s10);
      assert s11.stack[3] == 0x3d2;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[4] == 0x3d2;
      var s13 := Add(s12);
      assert s13.stack[3] == 0x3d2;
      var s14 := Swap(s13, 1);
      assert s14.stack[3] == 0x3d2;
      var s15 := Dup(s14, 2);
      assert s15.stack[4] == 0x3d2;
      var s16 := MStore(s15);
      assert s16.stack[2] == 0x3d2;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[3] == 0x3d2;
      var s18 := Add(s17);
      assert s18.stack[2] == 0x3d2;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[3] == 0x3d2;
      var s20 := Keccak256(s19);
      assert s20.stack[2] == 0x3d2;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[3] == 0x3d2;
      var s22 := Dup(s21, 3);
      assert s22.stack[4] == 0x3d2;
      var s23 := Dup(s22, 3);
      assert s23.stack[5] == 0x3d2;
      var s24 := SLoad(s23);
      assert s24.stack[5] == 0x3d2;
      var s25 := Add(s24);
      assert s25.stack[4] == 0x3d2;
      var s26 := Swap(s25, 3);
      assert s26.stack[4] == 0x3d2;
      var s27 := Pop(s26);
      assert s27.stack[3] == 0x3d2;
      var s28 := Pop(s27);
      assert s28.stack[2] == 0x3d2;
      var s29 := Dup(s28, 2);
      assert s29.stack[3] == 0x3d2;
      var s30 := Swap(s29, 1);
      assert s30.stack[3] == 0x3d2;
      var s31 := SStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s23(s31, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 70
    * Starting at 0x48d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x3d2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[0] == 0x3d2;
      var s2 := Caller(s1);
      assert s2.stack[1] == 0x3d2;
      var s3 := PushN(s2, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s3.stack[2] == 0x3d2;
      var s4 := And(s3);
      assert s4.stack[1] == 0x3d2;
      var s5 := PushN(s4, 32, 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c);
      assert s5.stack[2] == 0x3d2;
      var s6 := CallValue(s5);
      assert s6.stack[3] == 0x3d2;
      var s7 := PushN(s6, 1, 0x40);
      assert s7.stack[4] == 0x3d2;
      var s8 := MLoad(s7);
      assert s8.stack[4] == 0x3d2;
      var s9 := Dup(s8, 1);
      assert s9.stack[5] == 0x3d2;
      var s10 := Dup(s9, 3);
      assert s10.stack[6] == 0x3d2;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x3d2;
      var s12 := MStore(s11);
      assert s12.stack[5] == 0x3d2;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[6] == 0x3d2;
      var s14 := Add(s13);
      assert s14.stack[5] == 0x3d2;
      var s15 := Swap(s14, 2);
      assert s15.stack[5] == 0x3d2;
      var s16 := Pop(s15);
      assert s16.stack[4] == 0x3d2;
      var s17 := Pop(s16);
      assert s17.stack[3] == 0x3d2;
      var s18 := PushN(s17, 1, 0x40);
      assert s18.stack[4] == 0x3d2;
      var s19 := MLoad(s18);
      assert s19.stack[4] == 0x3d2;
      var s20 := Dup(s19, 1);
      assert s20.stack[5] == 0x3d2;
      var s21 := Swap(s20, 2);
      assert s21.stack[5] == 0x3d2;
      var s22 := Sub(s21);
      assert s22.stack[4] == 0x3d2;
      var s23 := Swap(s22, 1);
      assert s23.stack[4] == 0x3d2;
      var s24 := LogN(s23, 2);
      assert s24.stack[0] == 0x3d2;
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s25, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 64
    * Starting at 0x3d2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d2 as nat
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

  /** Node 25
    * Segment Id for this node is: 59
    * Starting at 0x370
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x370 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x037b);
      assert s4.stack[0] == 0x37b;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s5, gas - 1)
      else
        ExecuteFromCFGNode_s26(s5, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 60
    * Starting at 0x377
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x377 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 27
    * Segment Id for this node is: 61
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x03b0);
      assert s2.stack[0] == 0x3b0;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[1] == 0x3b0;
      var s4 := Dup(s3, 1);
      assert s4.stack[2] == 0x3b0;
      var s5 := Dup(s4, 1);
      assert s5.stack[3] == 0x3b0;
      var s6 := CallDataLoad(s5);
      assert s6.stack[3] == 0x3b0;
      var s7 := PushN(s6, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s7.stack[4] == 0x3b0;
      var s8 := And(s7);
      assert s8.stack[3] == 0x3b0;
      var s9 := Swap(s8, 1);
      assert s9.stack[3] == 0x3b0;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[4] == 0x3b0;
      var s11 := Add(s10);
      assert s11.stack[3] == 0x3b0;
      var s12 := Swap(s11, 1);
      assert s12.stack[3] == 0x3b0;
      var s13 := Swap(s12, 2);
      assert s13.stack[3] == 0x3b0;
      var s14 := Swap(s13, 1);
      assert s14.stack[3] == 0x3b0;
      var s15 := Dup(s14, 1);
      assert s15.stack[4] == 0x3b0;
      var s16 := CallDataLoad(s15);
      assert s16.stack[4] == 0x3b0;
      var s17 := Swap(s16, 1);
      assert s17.stack[4] == 0x3b0;
      var s18 := PushN(s17, 1, 0x20);
      assert s18.stack[5] == 0x3b0;
      var s19 := Add(s18);
      assert s19.stack[4] == 0x3b0;
      var s20 := Swap(s19, 1);
      assert s20.stack[4] == 0x3b0;
      var s21 := Swap(s20, 2);
      assert s21.stack[4] == 0x3b0;
      var s22 := Swap(s21, 1);
      assert s22.stack[4] == 0x3b0;
      var s23 := Pop(s22);
      assert s23.stack[3] == 0x3b0;
      var s24 := Pop(s23);
      assert s24.stack[2] == 0x3b0;
      var s25 := PushN(s24, 2, 0x0bce);
      assert s25.stack[0] == 0xbce;
      assert s25.stack[3] == 0x3b0;
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s26, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 115
    * Starting at 0xbce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x3b0;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[3] == 0x3b0;
      var s3 := PushN(s2, 2, 0x0bdb);
      assert s3.stack[0] == 0xbdb;
      assert s3.stack[4] == 0x3b0;
      var s4 := Caller(s3);
      assert s4.stack[1] == 0xbdb;
      assert s4.stack[5] == 0x3b0;
      var s5 := Dup(s4, 5);
      assert s5.stack[2] == 0xbdb;
      assert s5.stack[6] == 0x3b0;
      var s6 := Dup(s5, 5);
      assert s6.stack[3] == 0xbdb;
      assert s6.stack[7] == 0x3b0;
      var s7 := PushN(s6, 2, 0x068c);
      assert s7.stack[0] == 0x68c;
      assert s7.stack[4] == 0xbdb;
      assert s7.stack[8] == 0x3b0;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s8, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 83
    * Starting at 0x68c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xbdb

    requires s0.stack[7] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0xbdb;
      assert s1.stack[7] == 0x3b0;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[4] == 0xbdb;
      assert s2.stack[8] == 0x3b0;
      var s3 := Dup(s2, 2);
      assert s3.stack[5] == 0xbdb;
      assert s3.stack[9] == 0x3b0;
      var s4 := PushN(s3, 1, 0x03);
      assert s4.stack[6] == 0xbdb;
      assert s4.stack[10] == 0x3b0;
      var s5 := PushN(s4, 1, 0x00);
      assert s5.stack[7] == 0xbdb;
      assert s5.stack[11] == 0x3b0;
      var s6 := Dup(s5, 7);
      assert s6.stack[8] == 0xbdb;
      assert s6.stack[12] == 0x3b0;
      var s7 := PushN(s6, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s7.stack[9] == 0xbdb;
      assert s7.stack[13] == 0x3b0;
      var s8 := And(s7);
      assert s8.stack[8] == 0xbdb;
      assert s8.stack[12] == 0x3b0;
      var s9 := PushN(s8, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s9.stack[9] == 0xbdb;
      assert s9.stack[13] == 0x3b0;
      var s10 := And(s9);
      assert s10.stack[8] == 0xbdb;
      assert s10.stack[12] == 0x3b0;
      var s11 := Dup(s10, 2);
      assert s11.stack[9] == 0xbdb;
      assert s11.stack[13] == 0x3b0;
      var s12 := MStore(s11);
      assert s12.stack[7] == 0xbdb;
      assert s12.stack[11] == 0x3b0;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[8] == 0xbdb;
      assert s13.stack[12] == 0x3b0;
      var s14 := Add(s13);
      assert s14.stack[7] == 0xbdb;
      assert s14.stack[11] == 0x3b0;
      var s15 := Swap(s14, 1);
      assert s15.stack[7] == 0xbdb;
      assert s15.stack[11] == 0x3b0;
      var s16 := Dup(s15, 2);
      assert s16.stack[8] == 0xbdb;
      assert s16.stack[12] == 0x3b0;
      var s17 := MStore(s16);
      assert s17.stack[6] == 0xbdb;
      assert s17.stack[10] == 0x3b0;
      var s18 := PushN(s17, 1, 0x20);
      assert s18.stack[7] == 0xbdb;
      assert s18.stack[11] == 0x3b0;
      var s19 := Add(s18);
      assert s19.stack[6] == 0xbdb;
      assert s19.stack[10] == 0x3b0;
      var s20 := PushN(s19, 1, 0x00);
      assert s20.stack[7] == 0xbdb;
      assert s20.stack[11] == 0x3b0;
      var s21 := Keccak256(s20);
      assert s21.stack[6] == 0xbdb;
      assert s21.stack[10] == 0x3b0;
      var s22 := SLoad(s21);
      assert s22.stack[6] == 0xbdb;
      assert s22.stack[10] == 0x3b0;
      var s23 := Lt(s22);
      assert s23.stack[5] == 0xbdb;
      assert s23.stack[9] == 0x3b0;
      var s24 := IsZero(s23);
      assert s24.stack[5] == 0xbdb;
      assert s24.stack[9] == 0x3b0;
      var s25 := IsZero(s24);
      assert s25.stack[5] == 0xbdb;
      assert s25.stack[9] == 0x3b0;
      var s26 := IsZero(s25);
      assert s26.stack[5] == 0xbdb;
      assert s26.stack[9] == 0x3b0;
      var s27 := PushN(s26, 2, 0x06dc);
      assert s27.stack[0] == 0x6dc;
      assert s27.stack[6] == 0xbdb;
      assert s27.stack[10] == 0x3b0;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s28, gas - 1)
      else
        ExecuteFromCFGNode_s30(s28, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 84
    * Starting at 0x6d8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xbdb

    requires s0.stack[8] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0xbdb;
      assert s1.stack[9] == 0x3b0;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0xbdb;
      assert s2.stack[10] == 0x3b0;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 31
    * Segment Id for this node is: 85
    * Starting at 0x6dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xbdb

    requires s0.stack[8] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0xbdb;
      assert s1.stack[8] == 0x3b0;
      var s2 := Caller(s1);
      assert s2.stack[5] == 0xbdb;
      assert s2.stack[9] == 0x3b0;
      var s3 := PushN(s2, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s3.stack[6] == 0xbdb;
      assert s3.stack[10] == 0x3b0;
      var s4 := And(s3);
      assert s4.stack[5] == 0xbdb;
      assert s4.stack[9] == 0x3b0;
      var s5 := Dup(s4, 5);
      assert s5.stack[6] == 0xbdb;
      assert s5.stack[10] == 0x3b0;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[7] == 0xbdb;
      assert s6.stack[11] == 0x3b0;
      var s7 := And(s6);
      assert s7.stack[6] == 0xbdb;
      assert s7.stack[10] == 0x3b0;
      var s8 := Eq(s7);
      assert s8.stack[5] == 0xbdb;
      assert s8.stack[9] == 0x3b0;
      var s9 := IsZero(s8);
      assert s9.stack[5] == 0xbdb;
      assert s9.stack[9] == 0x3b0;
      var s10 := Dup(s9, 1);
      assert s10.stack[6] == 0xbdb;
      assert s10.stack[10] == 0x3b0;
      var s11 := IsZero(s10);
      assert s11.stack[6] == 0xbdb;
      assert s11.stack[10] == 0x3b0;
      var s12 := PushN(s11, 2, 0x07b4);
      assert s12.stack[0] == 0x7b4;
      assert s12.stack[7] == 0xbdb;
      assert s12.stack[11] == 0x3b0;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s13, gas - 1)
      else
        ExecuteFromCFGNode_s32(s13, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 86
    * Starting at 0x713
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x713 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xbdb

    requires s0.stack[9] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[4] == 0xbdb;
      assert s1.stack[8] == 0x3b0;
      var s2 := PushN(s1, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s2.stack[5] == 0xbdb;
      assert s2.stack[9] == 0x3b0;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[6] == 0xbdb;
      assert s3.stack[10] == 0x3b0;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[7] == 0xbdb;
      assert s4.stack[11] == 0x3b0;
      var s5 := Dup(s4, 7);
      assert s5.stack[8] == 0xbdb;
      assert s5.stack[12] == 0x3b0;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[9] == 0xbdb;
      assert s6.stack[13] == 0x3b0;
      var s7 := And(s6);
      assert s7.stack[8] == 0xbdb;
      assert s7.stack[12] == 0x3b0;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[9] == 0xbdb;
      assert s8.stack[13] == 0x3b0;
      var s9 := And(s8);
      assert s9.stack[8] == 0xbdb;
      assert s9.stack[12] == 0x3b0;
      var s10 := Dup(s9, 2);
      assert s10.stack[9] == 0xbdb;
      assert s10.stack[13] == 0x3b0;
      var s11 := MStore(s10);
      assert s11.stack[7] == 0xbdb;
      assert s11.stack[11] == 0x3b0;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[8] == 0xbdb;
      assert s12.stack[12] == 0x3b0;
      var s13 := Add(s12);
      assert s13.stack[7] == 0xbdb;
      assert s13.stack[11] == 0x3b0;
      var s14 := Swap(s13, 1);
      assert s14.stack[7] == 0xbdb;
      assert s14.stack[11] == 0x3b0;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0xbdb;
      assert s15.stack[12] == 0x3b0;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0xbdb;
      assert s16.stack[10] == 0x3b0;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0xbdb;
      assert s17.stack[11] == 0x3b0;
      var s18 := Add(s17);
      assert s18.stack[6] == 0xbdb;
      assert s18.stack[10] == 0x3b0;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[7] == 0xbdb;
      assert s19.stack[11] == 0x3b0;
      var s20 := Keccak256(s19);
      assert s20.stack[6] == 0xbdb;
      assert s20.stack[10] == 0x3b0;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[7] == 0xbdb;
      assert s21.stack[11] == 0x3b0;
      var s22 := Caller(s21);
      assert s22.stack[8] == 0xbdb;
      assert s22.stack[12] == 0x3b0;
      var s23 := PushN(s22, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s23.stack[9] == 0xbdb;
      assert s23.stack[13] == 0x3b0;
      var s24 := And(s23);
      assert s24.stack[8] == 0xbdb;
      assert s24.stack[12] == 0x3b0;
      var s25 := PushN(s24, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s25.stack[9] == 0xbdb;
      assert s25.stack[13] == 0x3b0;
      var s26 := And(s25);
      assert s26.stack[8] == 0xbdb;
      assert s26.stack[12] == 0x3b0;
      var s27 := Dup(s26, 2);
      assert s27.stack[9] == 0xbdb;
      assert s27.stack[13] == 0x3b0;
      var s28 := MStore(s27);
      assert s28.stack[7] == 0xbdb;
      assert s28.stack[11] == 0x3b0;
      var s29 := PushN(s28, 1, 0x20);
      assert s29.stack[8] == 0xbdb;
      assert s29.stack[12] == 0x3b0;
      var s30 := Add(s29);
      assert s30.stack[7] == 0xbdb;
      assert s30.stack[11] == 0x3b0;
      var s31 := Swap(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s33(s31, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 87
    * Starting at 0x7a9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0xbdb

    requires s0.stack[11] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[8] == 0xbdb;
      assert s1.stack[12] == 0x3b0;
      var s2 := MStore(s1);
      assert s2.stack[6] == 0xbdb;
      assert s2.stack[10] == 0x3b0;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[7] == 0xbdb;
      assert s3.stack[11] == 0x3b0;
      var s4 := Add(s3);
      assert s4.stack[6] == 0xbdb;
      assert s4.stack[10] == 0x3b0;
      var s5 := PushN(s4, 1, 0x00);
      assert s5.stack[7] == 0xbdb;
      assert s5.stack[11] == 0x3b0;
      var s6 := Keccak256(s5);
      assert s6.stack[6] == 0xbdb;
      assert s6.stack[10] == 0x3b0;
      var s7 := SLoad(s6);
      assert s7.stack[6] == 0xbdb;
      assert s7.stack[10] == 0x3b0;
      var s8 := Eq(s7);
      assert s8.stack[5] == 0xbdb;
      assert s8.stack[9] == 0x3b0;
      var s9 := IsZero(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s34(s9, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 88
    * Starting at 0x7b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xbdb

    requires s0.stack[9] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0xbdb;
      assert s1.stack[9] == 0x3b0;
      var s2 := IsZero(s1);
      assert s2.stack[5] == 0xbdb;
      assert s2.stack[9] == 0x3b0;
      var s3 := PushN(s2, 2, 0x08cf);
      assert s3.stack[0] == 0x8cf;
      assert s3.stack[6] == 0xbdb;
      assert s3.stack[10] == 0x3b0;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s40(s4, gas - 1)
      else
        ExecuteFromCFGNode_s35(s4, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 89
    * Starting at 0x7ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xbdb

    requires s0.stack[8] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[5] == 0xbdb;
      assert s1.stack[9] == 0x3b0;
      var s2 := PushN(s1, 1, 0x04);
      assert s2.stack[6] == 0xbdb;
      assert s2.stack[10] == 0x3b0;
      var s3 := PushN(s2, 1, 0x00);
      assert s3.stack[7] == 0xbdb;
      assert s3.stack[11] == 0x3b0;
      var s4 := Dup(s3, 7);
      assert s4.stack[8] == 0xbdb;
      assert s4.stack[12] == 0x3b0;
      var s5 := PushN(s4, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s5.stack[9] == 0xbdb;
      assert s5.stack[13] == 0x3b0;
      var s6 := And(s5);
      assert s6.stack[8] == 0xbdb;
      assert s6.stack[12] == 0x3b0;
      var s7 := PushN(s6, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s7.stack[9] == 0xbdb;
      assert s7.stack[13] == 0x3b0;
      var s8 := And(s7);
      assert s8.stack[8] == 0xbdb;
      assert s8.stack[12] == 0x3b0;
      var s9 := Dup(s8, 2);
      assert s9.stack[9] == 0xbdb;
      assert s9.stack[13] == 0x3b0;
      var s10 := MStore(s9);
      assert s10.stack[7] == 0xbdb;
      assert s10.stack[11] == 0x3b0;
      var s11 := PushN(s10, 1, 0x20);
      assert s11.stack[8] == 0xbdb;
      assert s11.stack[12] == 0x3b0;
      var s12 := Add(s11);
      assert s12.stack[7] == 0xbdb;
      assert s12.stack[11] == 0x3b0;
      var s13 := Swap(s12, 1);
      assert s13.stack[7] == 0xbdb;
      assert s13.stack[11] == 0x3b0;
      var s14 := Dup(s13, 2);
      assert s14.stack[8] == 0xbdb;
      assert s14.stack[12] == 0x3b0;
      var s15 := MStore(s14);
      assert s15.stack[6] == 0xbdb;
      assert s15.stack[10] == 0x3b0;
      var s16 := PushN(s15, 1, 0x20);
      assert s16.stack[7] == 0xbdb;
      assert s16.stack[11] == 0x3b0;
      var s17 := Add(s16);
      assert s17.stack[6] == 0xbdb;
      assert s17.stack[10] == 0x3b0;
      var s18 := PushN(s17, 1, 0x00);
      assert s18.stack[7] == 0xbdb;
      assert s18.stack[11] == 0x3b0;
      var s19 := Keccak256(s18);
      assert s19.stack[6] == 0xbdb;
      assert s19.stack[10] == 0x3b0;
      var s20 := PushN(s19, 1, 0x00);
      assert s20.stack[7] == 0xbdb;
      assert s20.stack[11] == 0x3b0;
      var s21 := Caller(s20);
      assert s21.stack[8] == 0xbdb;
      assert s21.stack[12] == 0x3b0;
      var s22 := PushN(s21, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s22.stack[9] == 0xbdb;
      assert s22.stack[13] == 0x3b0;
      var s23 := And(s22);
      assert s23.stack[8] == 0xbdb;
      assert s23.stack[12] == 0x3b0;
      var s24 := PushN(s23, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s24.stack[9] == 0xbdb;
      assert s24.stack[13] == 0x3b0;
      var s25 := And(s24);
      assert s25.stack[8] == 0xbdb;
      assert s25.stack[12] == 0x3b0;
      var s26 := Dup(s25, 2);
      assert s26.stack[9] == 0xbdb;
      assert s26.stack[13] == 0x3b0;
      var s27 := MStore(s26);
      assert s27.stack[7] == 0xbdb;
      assert s27.stack[11] == 0x3b0;
      var s28 := PushN(s27, 1, 0x20);
      assert s28.stack[8] == 0xbdb;
      assert s28.stack[12] == 0x3b0;
      var s29 := Add(s28);
      assert s29.stack[7] == 0xbdb;
      assert s29.stack[11] == 0x3b0;
      var s30 := Swap(s29, 1);
      assert s30.stack[7] == 0xbdb;
      assert s30.stack[11] == 0x3b0;
      var s31 := Dup(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s36(s31, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 90
    * Starting at 0x830
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x830 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0xbdb

    requires s0.stack[12] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.stack[6] == 0xbdb;
      assert s1.stack[10] == 0x3b0;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0xbdb;
      assert s2.stack[11] == 0x3b0;
      var s3 := Add(s2);
      assert s3.stack[6] == 0xbdb;
      assert s3.stack[10] == 0x3b0;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[7] == 0xbdb;
      assert s4.stack[11] == 0x3b0;
      var s5 := Keccak256(s4);
      assert s5.stack[6] == 0xbdb;
      assert s5.stack[10] == 0x3b0;
      var s6 := SLoad(s5);
      assert s6.stack[6] == 0xbdb;
      assert s6.stack[10] == 0x3b0;
      var s7 := Lt(s6);
      assert s7.stack[5] == 0xbdb;
      assert s7.stack[9] == 0x3b0;
      var s8 := IsZero(s7);
      assert s8.stack[5] == 0xbdb;
      assert s8.stack[9] == 0x3b0;
      var s9 := IsZero(s8);
      assert s9.stack[5] == 0xbdb;
      assert s9.stack[9] == 0x3b0;
      var s10 := IsZero(s9);
      assert s10.stack[5] == 0xbdb;
      assert s10.stack[9] == 0x3b0;
      var s11 := PushN(s10, 2, 0x0844);
      assert s11.stack[0] == 0x844;
      assert s11.stack[6] == 0xbdb;
      assert s11.stack[10] == 0x3b0;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s12, gas - 1)
      else
        ExecuteFromCFGNode_s37(s12, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 91
    * Starting at 0x840
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x840 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xbdb

    requires s0.stack[8] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0xbdb;
      assert s1.stack[9] == 0x3b0;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0xbdb;
      assert s2.stack[10] == 0x3b0;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 38
    * Segment Id for this node is: 92
    * Starting at 0x844
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x844 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xbdb

    requires s0.stack[8] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0xbdb;
      assert s1.stack[8] == 0x3b0;
      var s2 := Dup(s1, 2);
      assert s2.stack[5] == 0xbdb;
      assert s2.stack[9] == 0x3b0;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[6] == 0xbdb;
      assert s3.stack[10] == 0x3b0;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[7] == 0xbdb;
      assert s4.stack[11] == 0x3b0;
      var s5 := Dup(s4, 7);
      assert s5.stack[8] == 0xbdb;
      assert s5.stack[12] == 0x3b0;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[9] == 0xbdb;
      assert s6.stack[13] == 0x3b0;
      var s7 := And(s6);
      assert s7.stack[8] == 0xbdb;
      assert s7.stack[12] == 0x3b0;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[9] == 0xbdb;
      assert s8.stack[13] == 0x3b0;
      var s9 := And(s8);
      assert s9.stack[8] == 0xbdb;
      assert s9.stack[12] == 0x3b0;
      var s10 := Dup(s9, 2);
      assert s10.stack[9] == 0xbdb;
      assert s10.stack[13] == 0x3b0;
      var s11 := MStore(s10);
      assert s11.stack[7] == 0xbdb;
      assert s11.stack[11] == 0x3b0;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[8] == 0xbdb;
      assert s12.stack[12] == 0x3b0;
      var s13 := Add(s12);
      assert s13.stack[7] == 0xbdb;
      assert s13.stack[11] == 0x3b0;
      var s14 := Swap(s13, 1);
      assert s14.stack[7] == 0xbdb;
      assert s14.stack[11] == 0x3b0;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0xbdb;
      assert s15.stack[12] == 0x3b0;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0xbdb;
      assert s16.stack[10] == 0x3b0;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0xbdb;
      assert s17.stack[11] == 0x3b0;
      var s18 := Add(s17);
      assert s18.stack[6] == 0xbdb;
      assert s18.stack[10] == 0x3b0;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[7] == 0xbdb;
      assert s19.stack[11] == 0x3b0;
      var s20 := Keccak256(s19);
      assert s20.stack[6] == 0xbdb;
      assert s20.stack[10] == 0x3b0;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[7] == 0xbdb;
      assert s21.stack[11] == 0x3b0;
      var s22 := Caller(s21);
      assert s22.stack[8] == 0xbdb;
      assert s22.stack[12] == 0x3b0;
      var s23 := PushN(s22, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s23.stack[9] == 0xbdb;
      assert s23.stack[13] == 0x3b0;
      var s24 := And(s23);
      assert s24.stack[8] == 0xbdb;
      assert s24.stack[12] == 0x3b0;
      var s25 := PushN(s24, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s25.stack[9] == 0xbdb;
      assert s25.stack[13] == 0x3b0;
      var s26 := And(s25);
      assert s26.stack[8] == 0xbdb;
      assert s26.stack[12] == 0x3b0;
      var s27 := Dup(s26, 2);
      assert s27.stack[9] == 0xbdb;
      assert s27.stack[13] == 0x3b0;
      var s28 := MStore(s27);
      assert s28.stack[7] == 0xbdb;
      assert s28.stack[11] == 0x3b0;
      var s29 := PushN(s28, 1, 0x20);
      assert s29.stack[8] == 0xbdb;
      assert s29.stack[12] == 0x3b0;
      var s30 := Add(s29);
      assert s30.stack[7] == 0xbdb;
      assert s30.stack[11] == 0x3b0;
      var s31 := Swap(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s39(s31, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 93
    * Starting at 0x8ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0xbdb

    requires s0.stack[11] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[8] == 0xbdb;
      assert s1.stack[12] == 0x3b0;
      var s2 := MStore(s1);
      assert s2.stack[6] == 0xbdb;
      assert s2.stack[10] == 0x3b0;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[7] == 0xbdb;
      assert s3.stack[11] == 0x3b0;
      var s4 := Add(s3);
      assert s4.stack[6] == 0xbdb;
      assert s4.stack[10] == 0x3b0;
      var s5 := PushN(s4, 1, 0x00);
      assert s5.stack[7] == 0xbdb;
      assert s5.stack[11] == 0x3b0;
      var s6 := Keccak256(s5);
      assert s6.stack[6] == 0xbdb;
      assert s6.stack[10] == 0x3b0;
      var s7 := PushN(s6, 1, 0x00);
      assert s7.stack[7] == 0xbdb;
      assert s7.stack[11] == 0x3b0;
      var s8 := Dup(s7, 3);
      assert s8.stack[8] == 0xbdb;
      assert s8.stack[12] == 0x3b0;
      var s9 := Dup(s8, 3);
      assert s9.stack[9] == 0xbdb;
      assert s9.stack[13] == 0x3b0;
      var s10 := SLoad(s9);
      assert s10.stack[9] == 0xbdb;
      assert s10.stack[13] == 0x3b0;
      var s11 := Sub(s10);
      assert s11.stack[8] == 0xbdb;
      assert s11.stack[12] == 0x3b0;
      var s12 := Swap(s11, 3);
      assert s12.stack[8] == 0xbdb;
      assert s12.stack[12] == 0x3b0;
      var s13 := Pop(s12);
      assert s13.stack[7] == 0xbdb;
      assert s13.stack[11] == 0x3b0;
      var s14 := Pop(s13);
      assert s14.stack[6] == 0xbdb;
      assert s14.stack[10] == 0x3b0;
      var s15 := Dup(s14, 2);
      assert s15.stack[7] == 0xbdb;
      assert s15.stack[11] == 0x3b0;
      var s16 := Swap(s15, 1);
      assert s16.stack[7] == 0xbdb;
      assert s16.stack[11] == 0x3b0;
      var s17 := SStore(s16);
      assert s17.stack[5] == 0xbdb;
      assert s17.stack[9] == 0x3b0;
      var s18 := Pop(s17);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s40(s18, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 94
    * Starting at 0x8cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xbdb

    requires s0.stack[8] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0xbdb;
      assert s1.stack[8] == 0x3b0;
      var s2 := Dup(s1, 2);
      assert s2.stack[5] == 0xbdb;
      assert s2.stack[9] == 0x3b0;
      var s3 := PushN(s2, 1, 0x03);
      assert s3.stack[6] == 0xbdb;
      assert s3.stack[10] == 0x3b0;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[7] == 0xbdb;
      assert s4.stack[11] == 0x3b0;
      var s5 := Dup(s4, 7);
      assert s5.stack[8] == 0xbdb;
      assert s5.stack[12] == 0x3b0;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[9] == 0xbdb;
      assert s6.stack[13] == 0x3b0;
      var s7 := And(s6);
      assert s7.stack[8] == 0xbdb;
      assert s7.stack[12] == 0x3b0;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[9] == 0xbdb;
      assert s8.stack[13] == 0x3b0;
      var s9 := And(s8);
      assert s9.stack[8] == 0xbdb;
      assert s9.stack[12] == 0x3b0;
      var s10 := Dup(s9, 2);
      assert s10.stack[9] == 0xbdb;
      assert s10.stack[13] == 0x3b0;
      var s11 := MStore(s10);
      assert s11.stack[7] == 0xbdb;
      assert s11.stack[11] == 0x3b0;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[8] == 0xbdb;
      assert s12.stack[12] == 0x3b0;
      var s13 := Add(s12);
      assert s13.stack[7] == 0xbdb;
      assert s13.stack[11] == 0x3b0;
      var s14 := Swap(s13, 1);
      assert s14.stack[7] == 0xbdb;
      assert s14.stack[11] == 0x3b0;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0xbdb;
      assert s15.stack[12] == 0x3b0;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0xbdb;
      assert s16.stack[10] == 0x3b0;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0xbdb;
      assert s17.stack[11] == 0x3b0;
      var s18 := Add(s17);
      assert s18.stack[6] == 0xbdb;
      assert s18.stack[10] == 0x3b0;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[7] == 0xbdb;
      assert s19.stack[11] == 0x3b0;
      var s20 := Keccak256(s19);
      assert s20.stack[6] == 0xbdb;
      assert s20.stack[10] == 0x3b0;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[7] == 0xbdb;
      assert s21.stack[11] == 0x3b0;
      var s22 := Dup(s21, 3);
      assert s22.stack[8] == 0xbdb;
      assert s22.stack[12] == 0x3b0;
      var s23 := Dup(s22, 3);
      assert s23.stack[9] == 0xbdb;
      assert s23.stack[13] == 0x3b0;
      var s24 := SLoad(s23);
      assert s24.stack[9] == 0xbdb;
      assert s24.stack[13] == 0x3b0;
      var s25 := Sub(s24);
      assert s25.stack[8] == 0xbdb;
      assert s25.stack[12] == 0x3b0;
      var s26 := Swap(s25, 3);
      assert s26.stack[8] == 0xbdb;
      assert s26.stack[12] == 0x3b0;
      var s27 := Pop(s26);
      assert s27.stack[7] == 0xbdb;
      assert s27.stack[11] == 0x3b0;
      var s28 := Pop(s27);
      assert s28.stack[6] == 0xbdb;
      assert s28.stack[10] == 0x3b0;
      var s29 := Dup(s28, 2);
      assert s29.stack[7] == 0xbdb;
      assert s29.stack[11] == 0x3b0;
      var s30 := Swap(s29, 1);
      assert s30.stack[7] == 0xbdb;
      assert s30.stack[11] == 0x3b0;
      var s31 := SStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s41(s31, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 95
    * Starting at 0x91c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xbdb

    requires s0.stack[9] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[4] == 0xbdb;
      assert s1.stack[8] == 0x3b0;
      var s2 := Dup(s1, 2);
      assert s2.stack[5] == 0xbdb;
      assert s2.stack[9] == 0x3b0;
      var s3 := PushN(s2, 1, 0x03);
      assert s3.stack[6] == 0xbdb;
      assert s3.stack[10] == 0x3b0;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[7] == 0xbdb;
      assert s4.stack[11] == 0x3b0;
      var s5 := Dup(s4, 6);
      assert s5.stack[8] == 0xbdb;
      assert s5.stack[12] == 0x3b0;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[9] == 0xbdb;
      assert s6.stack[13] == 0x3b0;
      var s7 := And(s6);
      assert s7.stack[8] == 0xbdb;
      assert s7.stack[12] == 0x3b0;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[9] == 0xbdb;
      assert s8.stack[13] == 0x3b0;
      var s9 := And(s8);
      assert s9.stack[8] == 0xbdb;
      assert s9.stack[12] == 0x3b0;
      var s10 := Dup(s9, 2);
      assert s10.stack[9] == 0xbdb;
      assert s10.stack[13] == 0x3b0;
      var s11 := MStore(s10);
      assert s11.stack[7] == 0xbdb;
      assert s11.stack[11] == 0x3b0;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[8] == 0xbdb;
      assert s12.stack[12] == 0x3b0;
      var s13 := Add(s12);
      assert s13.stack[7] == 0xbdb;
      assert s13.stack[11] == 0x3b0;
      var s14 := Swap(s13, 1);
      assert s14.stack[7] == 0xbdb;
      assert s14.stack[11] == 0x3b0;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0xbdb;
      assert s15.stack[12] == 0x3b0;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0xbdb;
      assert s16.stack[10] == 0x3b0;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0xbdb;
      assert s17.stack[11] == 0x3b0;
      var s18 := Add(s17);
      assert s18.stack[6] == 0xbdb;
      assert s18.stack[10] == 0x3b0;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[7] == 0xbdb;
      assert s19.stack[11] == 0x3b0;
      var s20 := Keccak256(s19);
      assert s20.stack[6] == 0xbdb;
      assert s20.stack[10] == 0x3b0;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[7] == 0xbdb;
      assert s21.stack[11] == 0x3b0;
      var s22 := Dup(s21, 3);
      assert s22.stack[8] == 0xbdb;
      assert s22.stack[12] == 0x3b0;
      var s23 := Dup(s22, 3);
      assert s23.stack[9] == 0xbdb;
      assert s23.stack[13] == 0x3b0;
      var s24 := SLoad(s23);
      assert s24.stack[9] == 0xbdb;
      assert s24.stack[13] == 0x3b0;
      var s25 := Add(s24);
      assert s25.stack[8] == 0xbdb;
      assert s25.stack[12] == 0x3b0;
      var s26 := Swap(s25, 3);
      assert s26.stack[8] == 0xbdb;
      assert s26.stack[12] == 0x3b0;
      var s27 := Pop(s26);
      assert s27.stack[7] == 0xbdb;
      assert s27.stack[11] == 0x3b0;
      var s28 := Pop(s27);
      assert s28.stack[6] == 0xbdb;
      assert s28.stack[10] == 0x3b0;
      var s29 := Dup(s28, 2);
      assert s29.stack[7] == 0xbdb;
      assert s29.stack[11] == 0x3b0;
      var s30 := Swap(s29, 1);
      assert s30.stack[7] == 0xbdb;
      assert s30.stack[11] == 0x3b0;
      var s31 := SStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s42(s31, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 96
    * Starting at 0x969
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x969 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xbdb

    requires s0.stack[9] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[4] == 0xbdb;
      assert s1.stack[8] == 0x3b0;
      var s2 := Dup(s1, 3);
      assert s2.stack[5] == 0xbdb;
      assert s2.stack[9] == 0x3b0;
      var s3 := PushN(s2, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s3.stack[6] == 0xbdb;
      assert s3.stack[10] == 0x3b0;
      var s4 := And(s3);
      assert s4.stack[5] == 0xbdb;
      assert s4.stack[9] == 0x3b0;
      var s5 := Dup(s4, 5);
      assert s5.stack[6] == 0xbdb;
      assert s5.stack[10] == 0x3b0;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[7] == 0xbdb;
      assert s6.stack[11] == 0x3b0;
      var s7 := And(s6);
      assert s7.stack[6] == 0xbdb;
      assert s7.stack[10] == 0x3b0;
      var s8 := PushN(s7, 32, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      assert s8.stack[7] == 0xbdb;
      assert s8.stack[11] == 0x3b0;
      var s9 := Dup(s8, 5);
      assert s9.stack[8] == 0xbdb;
      assert s9.stack[12] == 0x3b0;
      var s10 := PushN(s9, 1, 0x40);
      assert s10.stack[9] == 0xbdb;
      assert s10.stack[13] == 0x3b0;
      var s11 := MLoad(s10);
      assert s11.stack[9] == 0xbdb;
      assert s11.stack[13] == 0x3b0;
      var s12 := Dup(s11, 1);
      assert s12.stack[10] == 0xbdb;
      assert s12.stack[14] == 0x3b0;
      var s13 := Dup(s12, 3);
      assert s13.stack[11] == 0xbdb;
      assert s13.stack[15] == 0x3b0;
      var s14 := Dup(s13, 2);
      assert s14.stack[12] == 0xbdb;
      assert s14.stack[16] == 0x3b0;
      var s15 := MStore(s14);
      assert s15.stack[10] == 0xbdb;
      assert s15.stack[14] == 0x3b0;
      var s16 := PushN(s15, 1, 0x20);
      assert s16.stack[11] == 0xbdb;
      assert s16.stack[15] == 0x3b0;
      var s17 := Add(s16);
      assert s17.stack[10] == 0xbdb;
      assert s17.stack[14] == 0x3b0;
      var s18 := Swap(s17, 2);
      assert s18.stack[10] == 0xbdb;
      assert s18.stack[14] == 0x3b0;
      var s19 := Pop(s18);
      assert s19.stack[9] == 0xbdb;
      assert s19.stack[13] == 0x3b0;
      var s20 := Pop(s19);
      assert s20.stack[8] == 0xbdb;
      assert s20.stack[12] == 0x3b0;
      var s21 := PushN(s20, 1, 0x40);
      assert s21.stack[9] == 0xbdb;
      assert s21.stack[13] == 0x3b0;
      var s22 := MLoad(s21);
      assert s22.stack[9] == 0xbdb;
      assert s22.stack[13] == 0x3b0;
      var s23 := Dup(s22, 1);
      assert s23.stack[10] == 0xbdb;
      assert s23.stack[14] == 0x3b0;
      var s24 := Swap(s23, 2);
      assert s24.stack[10] == 0xbdb;
      assert s24.stack[14] == 0x3b0;
      var s25 := Sub(s24);
      assert s25.stack[9] == 0xbdb;
      assert s25.stack[13] == 0x3b0;
      var s26 := Swap(s25, 1);
      assert s26.stack[9] == 0xbdb;
      assert s26.stack[13] == 0x3b0;
      var s27 := LogN(s26, 3);
      assert s27.stack[4] == 0xbdb;
      assert s27.stack[8] == 0x3b0;
      var s28 := PushN(s27, 1, 0x01);
      assert s28.stack[5] == 0xbdb;
      assert s28.stack[9] == 0x3b0;
      var s29 := Swap(s28, 1);
      assert s29.stack[5] == 0xbdb;
      assert s29.stack[9] == 0x3b0;
      var s30 := Pop(s29);
      assert s30.stack[4] == 0xbdb;
      assert s30.stack[8] == 0x3b0;
      var s31 := Swap(s30, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s43(s31, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 97
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0xbdb

    requires s0.stack[8] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[3] == 0xbdb;
      assert s1.stack[8] == 0x3b0;
      var s2 := Pop(s1);
      assert s2.stack[2] == 0xbdb;
      assert s2.stack[7] == 0x3b0;
      var s3 := Pop(s2);
      assert s3.stack[1] == 0xbdb;
      assert s3.stack[6] == 0x3b0;
      var s4 := Pop(s3);
      assert s4.stack[0] == 0xbdb;
      assert s4.stack[5] == 0x3b0;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s5, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 116
    * Starting at 0xbdb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x3b0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x3b0;
      var s2 := Swap(s1, 1);
      assert s2.stack[4] == 0x3b0;
      var s3 := Pop(s2);
      assert s3.stack[3] == 0x3b0;
      var s4 := Swap(s3, 3);
      assert s4.stack[0] == 0x3b0;
      var s5 := Swap(s4, 2);
      assert s5.stack[2] == 0x3b0;
      var s6 := Pop(s5);
      assert s6.stack[1] == 0x3b0;
      var s7 := Pop(s6);
      assert s7.stack[0] == 0x3b0;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s8, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 62
    * Starting at 0x3b0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := IsZero(s5);
      var s7 := IsZero(s6);
      var s8 := IsZero(s7);
      var s9 := IsZero(s8);
      var s10 := Dup(s9, 2);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Add(s12);
      var s14 := Swap(s13, 2);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := PushN(s16, 1, 0x40);
      var s18 := MLoad(s17);
      var s19 := Dup(s18, 1);
      var s20 := Swap(s19, 2);
      var s21 := Sub(s20);
      var s22 := Swap(s21, 1);
      var s23 := Return(s22);
      // Segment is terminal (Revert, Stop or Return)
      s23
  }

  /** Node 46
    * Segment Id for this node is: 49
    * Starting at 0x2e2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x02ed);
      assert s4.stack[0] == 0x2ed;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s5, gas - 1)
      else
        ExecuteFromCFGNode_s47(s5, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 50
    * Starting at 0x2e9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 48
    * Segment Id for this node is: 51
    * Starting at 0x2ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x02f5);
      assert s2.stack[0] == 0x2f5;
      var s3 := PushN(s2, 2, 0x0b30);
      assert s3.stack[0] == 0xb30;
      assert s3.stack[1] == 0x2f5;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s4, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 107
    * Starting at 0xb30
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0x2f5;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[1] == 0x2f5;
      var s3 := Dup(s2, 1);
      assert s3.stack[2] == 0x2f5;
      var s4 := SLoad(s3);
      assert s4.stack[2] == 0x2f5;
      var s5 := PushN(s4, 1, 0x01);
      assert s5.stack[3] == 0x2f5;
      var s6 := Dup(s5, 2);
      assert s6.stack[4] == 0x2f5;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[5] == 0x2f5;
      var s8 := And(s7);
      assert s8.stack[4] == 0x2f5;
      var s9 := IsZero(s8);
      assert s9.stack[4] == 0x2f5;
      var s10 := PushN(s9, 2, 0x0100);
      assert s10.stack[5] == 0x2f5;
      var s11 := Mul(s10);
      assert s11.stack[4] == 0x2f5;
      var s12 := Sub(s11);
      assert s12.stack[3] == 0x2f5;
      var s13 := And(s12);
      assert s13.stack[2] == 0x2f5;
      var s14 := PushN(s13, 1, 0x02);
      assert s14.stack[3] == 0x2f5;
      var s15 := Swap(s14, 1);
      assert s15.stack[3] == 0x2f5;
      var s16 := Div(s15);
      assert s16.stack[2] == 0x2f5;
      var s17 := Dup(s16, 1);
      assert s17.stack[3] == 0x2f5;
      var s18 := PushN(s17, 1, 0x1f);
      assert s18.stack[4] == 0x2f5;
      var s19 := Add(s18);
      assert s19.stack[3] == 0x2f5;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[4] == 0x2f5;
      var s21 := Dup(s20, 1);
      assert s21.stack[5] == 0x2f5;
      var s22 := Swap(s21, 2);
      assert s22.stack[5] == 0x2f5;
      var s23 := Div(s22);
      assert s23.stack[4] == 0x2f5;
      var s24 := Mul(s23);
      assert s24.stack[3] == 0x2f5;
      var s25 := PushN(s24, 1, 0x20);
      assert s25.stack[4] == 0x2f5;
      var s26 := Add(s25);
      assert s26.stack[3] == 0x2f5;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[4] == 0x2f5;
      var s28 := MLoad(s27);
      assert s28.stack[4] == 0x2f5;
      var s29 := Swap(s28, 1);
      assert s29.stack[4] == 0x2f5;
      var s30 := Dup(s29, 2);
      assert s30.stack[5] == 0x2f5;
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s50(s31, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 108
    * Starting at 0xb59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[5] == 0x2f5;
      var s2 := MStore(s1);
      assert s2.stack[3] == 0x2f5;
      var s3 := Dup(s2, 1);
      assert s3.stack[4] == 0x2f5;
      var s4 := Swap(s3, 3);
      assert s4.stack[4] == 0x2f5;
      var s5 := Swap(s4, 2);
      assert s5.stack[4] == 0x2f5;
      var s6 := Swap(s5, 1);
      assert s6.stack[4] == 0x2f5;
      var s7 := Dup(s6, 2);
      assert s7.stack[5] == 0x2f5;
      var s8 := Dup(s7, 2);
      assert s8.stack[6] == 0x2f5;
      var s9 := MStore(s8);
      assert s9.stack[4] == 0x2f5;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[5] == 0x2f5;
      var s11 := Add(s10);
      assert s11.stack[4] == 0x2f5;
      var s12 := Dup(s11, 3);
      assert s12.stack[5] == 0x2f5;
      var s13 := Dup(s12, 1);
      assert s13.stack[6] == 0x2f5;
      var s14 := SLoad(s13);
      assert s14.stack[6] == 0x2f5;
      var s15 := PushN(s14, 1, 0x01);
      assert s15.stack[7] == 0x2f5;
      var s16 := Dup(s15, 2);
      assert s16.stack[8] == 0x2f5;
      var s17 := PushN(s16, 1, 0x01);
      assert s17.stack[9] == 0x2f5;
      var s18 := And(s17);
      assert s18.stack[8] == 0x2f5;
      var s19 := IsZero(s18);
      assert s19.stack[8] == 0x2f5;
      var s20 := PushN(s19, 2, 0x0100);
      assert s20.stack[9] == 0x2f5;
      var s21 := Mul(s20);
      assert s21.stack[8] == 0x2f5;
      var s22 := Sub(s21);
      assert s22.stack[7] == 0x2f5;
      var s23 := And(s22);
      assert s23.stack[6] == 0x2f5;
      var s24 := PushN(s23, 1, 0x02);
      assert s24.stack[7] == 0x2f5;
      var s25 := Swap(s24, 1);
      assert s25.stack[7] == 0x2f5;
      var s26 := Div(s25);
      assert s26.stack[6] == 0x2f5;
      var s27 := Dup(s26, 1);
      assert s27.stack[7] == 0x2f5;
      var s28 := IsZero(s27);
      assert s28.stack[7] == 0x2f5;
      var s29 := PushN(s28, 2, 0x0bc6);
      assert s29.stack[0] == 0xbc6;
      assert s29.stack[8] == 0x2f5;
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s30, gas - 1)
      else
        ExecuteFromCFGNode_s51(s30, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 109
    * Starting at 0xb80
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[7] == 0x2f5;
      var s2 := PushN(s1, 1, 0x1f);
      assert s2.stack[8] == 0x2f5;
      var s3 := Lt(s2);
      assert s3.stack[7] == 0x2f5;
      var s4 := PushN(s3, 2, 0x0b9b);
      assert s4.stack[0] == 0xb9b;
      assert s4.stack[8] == 0x2f5;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s5, gas - 1)
      else
        ExecuteFromCFGNode_s52(s5, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 110
    * Starting at 0xb88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      assert s1.stack[7] == 0x2f5;
      var s2 := Dup(s1, 1);
      assert s2.stack[8] == 0x2f5;
      var s3 := Dup(s2, 4);
      assert s3.stack[9] == 0x2f5;
      var s4 := SLoad(s3);
      assert s4.stack[9] == 0x2f5;
      var s5 := Div(s4);
      assert s5.stack[8] == 0x2f5;
      var s6 := Mul(s5);
      assert s6.stack[7] == 0x2f5;
      var s7 := Dup(s6, 4);
      assert s7.stack[8] == 0x2f5;
      var s8 := MStore(s7);
      assert s8.stack[6] == 0x2f5;
      var s9 := Swap(s8, 2);
      assert s9.stack[6] == 0x2f5;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[7] == 0x2f5;
      var s11 := Add(s10);
      assert s11.stack[6] == 0x2f5;
      var s12 := Swap(s11, 2);
      assert s12.stack[6] == 0x2f5;
      var s13 := PushN(s12, 2, 0x0bc6);
      assert s13.stack[0] == 0xbc6;
      assert s13.stack[7] == 0x2f5;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s14, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 114
    * Starting at 0xbc6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x2f5;
      var s2 := Pop(s1);
      assert s2.stack[5] == 0x2f5;
      var s3 := Pop(s2);
      assert s3.stack[4] == 0x2f5;
      var s4 := Pop(s3);
      assert s4.stack[3] == 0x2f5;
      var s5 := Pop(s4);
      assert s5.stack[2] == 0x2f5;
      var s6 := Pop(s5);
      assert s6.stack[1] == 0x2f5;
      var s7 := Dup(s6, 2);
      assert s7.stack[0] == 0x2f5;
      assert s7.stack[2] == 0x2f5;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s8, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 52
    * Starting at 0x2f5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x2f5;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0x2f5;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x2f5;
      var s4 := Dup(s3, 1);
      assert s4.stack[3] == 0x2f5;
      var s5 := Dup(s4, 1);
      assert s5.stack[4] == 0x2f5;
      var s6 := PushN(s5, 1, 0x20);
      assert s6.stack[5] == 0x2f5;
      var s7 := Add(s6);
      assert s7.stack[4] == 0x2f5;
      var s8 := Dup(s7, 3);
      assert s8.stack[5] == 0x2f5;
      var s9 := Dup(s8, 2);
      assert s9.stack[6] == 0x2f5;
      var s10 := Sub(s9);
      assert s10.stack[5] == 0x2f5;
      var s11 := Dup(s10, 3);
      assert s11.stack[6] == 0x2f5;
      var s12 := MStore(s11);
      assert s12.stack[4] == 0x2f5;
      var s13 := Dup(s12, 4);
      assert s13.stack[5] == 0x2f5;
      var s14 := Dup(s13, 2);
      assert s14.stack[6] == 0x2f5;
      var s15 := Dup(s14, 2);
      assert s15.stack[7] == 0x2f5;
      var s16 := MLoad(s15);
      assert s16.stack[7] == 0x2f5;
      var s17 := Dup(s16, 2);
      assert s17.stack[8] == 0x2f5;
      var s18 := MStore(s17);
      assert s18.stack[6] == 0x2f5;
      var s19 := PushN(s18, 1, 0x20);
      assert s19.stack[7] == 0x2f5;
      var s20 := Add(s19);
      assert s20.stack[6] == 0x2f5;
      var s21 := Swap(s20, 2);
      assert s21.stack[6] == 0x2f5;
      var s22 := Pop(s21);
      assert s22.stack[5] == 0x2f5;
      var s23 := Dup(s22, 1);
      assert s23.stack[6] == 0x2f5;
      var s24 := MLoad(s23);
      assert s24.stack[6] == 0x2f5;
      var s25 := Swap(s24, 1);
      assert s25.stack[6] == 0x2f5;
      var s26 := PushN(s25, 1, 0x20);
      assert s26.stack[7] == 0x2f5;
      var s27 := Add(s26);
      assert s27.stack[6] == 0x2f5;
      var s28 := Swap(s27, 1);
      assert s28.stack[6] == 0x2f5;
      var s29 := Dup(s28, 1);
      assert s29.stack[7] == 0x2f5;
      var s30 := Dup(s29, 4);
      assert s30.stack[8] == 0x2f5;
      var s31 := Dup(s30, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s55(s31, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 53
    * Starting at 0x318
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x318 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s56(s1, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 54
    * Starting at 0x31a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[10] == 0x2f5;
      var s2 := Dup(s1, 4);
      assert s2.stack[11] == 0x2f5;
      var s3 := Dup(s2, 2);
      assert s3.stack[12] == 0x2f5;
      var s4 := Lt(s3);
      assert s4.stack[11] == 0x2f5;
      var s5 := IsZero(s4);
      assert s5.stack[11] == 0x2f5;
      var s6 := PushN(s5, 2, 0x0335);
      assert s6.stack[0] == 0x335;
      assert s6.stack[12] == 0x2f5;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s7, gas - 1)
      else
        ExecuteFromCFGNode_s57(s7, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 55
    * Starting at 0x323
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x323 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[11] == 0x2f5;
      var s2 := Dup(s1, 3);
      assert s2.stack[12] == 0x2f5;
      var s3 := Add(s2);
      assert s3.stack[11] == 0x2f5;
      var s4 := MLoad(s3);
      assert s4.stack[11] == 0x2f5;
      var s5 := Dup(s4, 2);
      assert s5.stack[12] == 0x2f5;
      var s6 := Dup(s5, 5);
      assert s6.stack[13] == 0x2f5;
      var s7 := Add(s6);
      assert s7.stack[12] == 0x2f5;
      var s8 := MStore(s7);
      assert s8.stack[10] == 0x2f5;
      var s9 := PushN(s8, 1, 0x20);
      assert s9.stack[11] == 0x2f5;
      var s10 := Dup(s9, 2);
      assert s10.stack[12] == 0x2f5;
      var s11 := Add(s10);
      assert s11.stack[11] == 0x2f5;
      var s12 := Swap(s11, 1);
      assert s12.stack[11] == 0x2f5;
      var s13 := Pop(s12);
      assert s13.stack[10] == 0x2f5;
      var s14 := PushN(s13, 2, 0x031a);
      assert s14.stack[0] == 0x31a;
      assert s14.stack[11] == 0x2f5;
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s15, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 56
    * Starting at 0x335
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x335 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[10] == 0x2f5;
      var s2 := Pop(s1);
      assert s2.stack[9] == 0x2f5;
      var s3 := Pop(s2);
      assert s3.stack[8] == 0x2f5;
      var s4 := Pop(s3);
      assert s4.stack[7] == 0x2f5;
      var s5 := Pop(s4);
      assert s5.stack[6] == 0x2f5;
      var s6 := Swap(s5, 1);
      assert s6.stack[6] == 0x2f5;
      var s7 := Pop(s6);
      assert s7.stack[5] == 0x2f5;
      var s8 := Swap(s7, 1);
      assert s8.stack[5] == 0x2f5;
      var s9 := Dup(s8, 2);
      assert s9.stack[6] == 0x2f5;
      var s10 := Add(s9);
      assert s10.stack[5] == 0x2f5;
      var s11 := Swap(s10, 1);
      assert s11.stack[5] == 0x2f5;
      var s12 := PushN(s11, 1, 0x1f);
      assert s12.stack[6] == 0x2f5;
      var s13 := And(s12);
      assert s13.stack[5] == 0x2f5;
      var s14 := Dup(s13, 1);
      assert s14.stack[6] == 0x2f5;
      var s15 := IsZero(s14);
      assert s15.stack[6] == 0x2f5;
      var s16 := PushN(s15, 2, 0x0362);
      assert s16.stack[0] == 0x362;
      assert s16.stack[7] == 0x2f5;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s17, gas - 1)
      else
        ExecuteFromCFGNode_s59(s17, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 57
    * Starting at 0x349
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x349 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[6] == 0x2f5;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0x2f5;
      var s3 := Sub(s2);
      assert s3.stack[6] == 0x2f5;
      var s4 := Dup(s3, 1);
      assert s4.stack[7] == 0x2f5;
      var s5 := MLoad(s4);
      assert s5.stack[7] == 0x2f5;
      var s6 := PushN(s5, 1, 0x01);
      assert s6.stack[8] == 0x2f5;
      var s7 := Dup(s6, 4);
      assert s7.stack[9] == 0x2f5;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[10] == 0x2f5;
      var s9 := Sub(s8);
      assert s9.stack[9] == 0x2f5;
      var s10 := PushN(s9, 2, 0x0100);
      assert s10.stack[10] == 0x2f5;
      var s11 := Exp(s10);
      assert s11.stack[9] == 0x2f5;
      var s12 := Sub(s11);
      assert s12.stack[8] == 0x2f5;
      var s13 := Not(s12);
      assert s13.stack[8] == 0x2f5;
      var s14 := And(s13);
      assert s14.stack[7] == 0x2f5;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0x2f5;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0x2f5;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0x2f5;
      var s18 := Add(s17);
      assert s18.stack[6] == 0x2f5;
      var s19 := Swap(s18, 2);
      assert s19.stack[6] == 0x2f5;
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s60(s20, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 58
    * Starting at 0x362
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x362 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x2f5;
      var s2 := Pop(s1);
      assert s2.stack[4] == 0x2f5;
      var s3 := Swap(s2, 3);
      assert s3.stack[4] == 0x2f5;
      var s4 := Pop(s3);
      assert s4.stack[3] == 0x2f5;
      var s5 := Pop(s4);
      assert s5.stack[2] == 0x2f5;
      var s6 := Pop(s5);
      assert s6.stack[1] == 0x2f5;
      var s7 := PushN(s6, 1, 0x40);
      assert s7.stack[2] == 0x2f5;
      var s8 := MLoad(s7);
      assert s8.stack[2] == 0x2f5;
      var s9 := Dup(s8, 1);
      assert s9.stack[3] == 0x2f5;
      var s10 := Swap(s9, 2);
      assert s10.stack[3] == 0x2f5;
      var s11 := Sub(s10);
      assert s11.stack[2] == 0x2f5;
      var s12 := Swap(s11, 1);
      assert s12.stack[2] == 0x2f5;
      var s13 := Return(s12);
      // Segment is terminal (Revert, Stop or Return)
      s13
  }

  /** Node 61
    * Segment Id for this node is: 111
    * Starting at 0xb9b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x2f5;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0x2f5;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x2f5;
      var s4 := Swap(s3, 2);
      assert s4.stack[6] == 0x2f5;
      var s5 := Swap(s4, 1);
      assert s5.stack[6] == 0x2f5;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[7] == 0x2f5;
      var s7 := MStore(s6);
      assert s7.stack[5] == 0x2f5;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[6] == 0x2f5;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[7] == 0x2f5;
      var s10 := Keccak256(s9);
      assert s10.stack[6] == 0x2f5;
      var s11 := Swap(s10, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s62(s11, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 112
    * Starting at 0xba9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x2f5;
      var s2 := Dup(s1, 2);
      assert s2.stack[7] == 0x2f5;
      var s3 := SLoad(s2);
      assert s3.stack[7] == 0x2f5;
      var s4 := Dup(s3, 2);
      assert s4.stack[8] == 0x2f5;
      var s5 := MStore(s4);
      assert s5.stack[6] == 0x2f5;
      var s6 := Swap(s5, 1);
      assert s6.stack[6] == 0x2f5;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[7] == 0x2f5;
      var s8 := Add(s7);
      assert s8.stack[6] == 0x2f5;
      var s9 := Swap(s8, 1);
      assert s9.stack[6] == 0x2f5;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[7] == 0x2f5;
      var s11 := Add(s10);
      assert s11.stack[6] == 0x2f5;
      var s12 := Dup(s11, 1);
      assert s12.stack[7] == 0x2f5;
      var s13 := Dup(s12, 4);
      assert s13.stack[8] == 0x2f5;
      var s14 := Gt(s13);
      assert s14.stack[7] == 0x2f5;
      var s15 := PushN(s14, 2, 0x0ba9);
      assert s15.stack[0] == 0xba9;
      assert s15.stack[8] == 0x2f5;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s62(s16, gas - 1)
      else
        ExecuteFromCFGNode_s63(s16, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 113
    * Starting at 0xbbd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x2f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[7] == 0x2f5;
      var s2 := Swap(s1, 1);
      assert s2.stack[7] == 0x2f5;
      var s3 := Sub(s2);
      assert s3.stack[6] == 0x2f5;
      var s4 := PushN(s3, 1, 0x1f);
      assert s4.stack[7] == 0x2f5;
      var s5 := And(s4);
      assert s5.stack[6] == 0x2f5;
      var s6 := Dup(s5, 3);
      assert s6.stack[7] == 0x2f5;
      var s7 := Add(s6);
      assert s7.stack[6] == 0x2f5;
      var s8 := Swap(s7, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s53(s8, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 45
    * Starting at 0x295
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x02a0);
      assert s4.stack[0] == 0x2a0;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s5, gas - 1)
      else
        ExecuteFromCFGNode_s65(s5, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 46
    * Starting at 0x29c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 66
    * Segment Id for this node is: 47
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x02cc);
      assert s2.stack[0] == 0x2cc;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[1] == 0x2cc;
      var s4 := Dup(s3, 1);
      assert s4.stack[2] == 0x2cc;
      var s5 := Dup(s4, 1);
      assert s5.stack[3] == 0x2cc;
      var s6 := CallDataLoad(s5);
      assert s6.stack[3] == 0x2cc;
      var s7 := PushN(s6, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s7.stack[4] == 0x2cc;
      var s8 := And(s7);
      assert s8.stack[3] == 0x2cc;
      var s9 := Swap(s8, 1);
      assert s9.stack[3] == 0x2cc;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[4] == 0x2cc;
      var s11 := Add(s10);
      assert s11.stack[3] == 0x2cc;
      var s12 := Swap(s11, 1);
      assert s12.stack[3] == 0x2cc;
      var s13 := Swap(s12, 2);
      assert s13.stack[3] == 0x2cc;
      var s14 := Swap(s13, 1);
      assert s14.stack[3] == 0x2cc;
      var s15 := Pop(s14);
      assert s15.stack[2] == 0x2cc;
      var s16 := Pop(s15);
      assert s16.stack[1] == 0x2cc;
      var s17 := PushN(s16, 2, 0x0b18);
      assert s17.stack[0] == 0xb18;
      assert s17.stack[2] == 0x2cc;
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s18, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 106
    * Starting at 0xb18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x2cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x2cc;
      var s2 := PushN(s1, 1, 0x03);
      assert s2.stack[2] == 0x2cc;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[3] == 0x2cc;
      var s4 := MStore(s3);
      assert s4.stack[1] == 0x2cc;
      var s5 := Dup(s4, 1);
      assert s5.stack[2] == 0x2cc;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[3] == 0x2cc;
      var s7 := MStore(s6);
      assert s7.stack[1] == 0x2cc;
      var s8 := PushN(s7, 1, 0x40);
      assert s8.stack[2] == 0x2cc;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[3] == 0x2cc;
      var s10 := Keccak256(s9);
      assert s10.stack[2] == 0x2cc;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[3] == 0x2cc;
      var s12 := Swap(s11, 2);
      assert s12.stack[3] == 0x2cc;
      var s13 := Pop(s12);
      assert s13.stack[2] == 0x2cc;
      var s14 := Swap(s13, 1);
      assert s14.stack[2] == 0x2cc;
      var s15 := Pop(s14);
      assert s15.stack[1] == 0x2cc;
      var s16 := SLoad(s15);
      assert s16.stack[1] == 0x2cc;
      var s17 := Dup(s16, 2);
      assert s17.stack[0] == 0x2cc;
      assert s17.stack[2] == 0x2cc;
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s18, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 48
    * Starting at 0x2cc
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x2cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x2cc;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0x2cc;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x2cc;
      var s4 := Dup(s3, 1);
      assert s4.stack[3] == 0x2cc;
      var s5 := Dup(s4, 3);
      assert s5.stack[4] == 0x2cc;
      var s6 := Dup(s5, 2);
      assert s6.stack[5] == 0x2cc;
      var s7 := MStore(s6);
      assert s7.stack[3] == 0x2cc;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[4] == 0x2cc;
      var s9 := Add(s8);
      assert s9.stack[3] == 0x2cc;
      var s10 := Swap(s9, 2);
      assert s10.stack[3] == 0x2cc;
      var s11 := Pop(s10);
      assert s11.stack[2] == 0x2cc;
      var s12 := Pop(s11);
      assert s12.stack[1] == 0x2cc;
      var s13 := PushN(s12, 1, 0x40);
      assert s13.stack[2] == 0x2cc;
      var s14 := MLoad(s13);
      assert s14.stack[2] == 0x2cc;
      var s15 := Dup(s14, 1);
      assert s15.stack[3] == 0x2cc;
      var s16 := Swap(s15, 2);
      assert s16.stack[3] == 0x2cc;
      var s17 := Sub(s16);
      assert s17.stack[2] == 0x2cc;
      var s18 := Swap(s17, 1);
      assert s18.stack[2] == 0x2cc;
      var s19 := Return(s18);
      // Segment is terminal (Revert, Stop or Return)
      s19
  }

  /** Node 69
    * Segment Id for this node is: 41
    * Starting at 0x266
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x266 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x0271);
      assert s4.stack[0] == 0x271;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s5, gas - 1)
      else
        ExecuteFromCFGNode_s70(s5, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 42
    * Starting at 0x26d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 71
    * Segment Id for this node is: 43
    * Starting at 0x271
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x271 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0279);
      assert s2.stack[0] == 0x279;
      var s3 := PushN(s2, 2, 0x0b05);
      assert s3.stack[0] == 0xb05;
      assert s3.stack[1] == 0x279;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s4, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 105
    * Starting at 0xb05
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x279

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0x279;
      var s2 := PushN(s1, 1, 0x02);
      assert s2.stack[1] == 0x279;
      var s3 := PushN(s2, 1, 0x00);
      assert s3.stack[2] == 0x279;
      var s4 := Swap(s3, 1);
      assert s4.stack[2] == 0x279;
      var s5 := SLoad(s4);
      assert s5.stack[2] == 0x279;
      var s6 := Swap(s5, 1);
      assert s6.stack[2] == 0x279;
      var s7 := PushN(s6, 2, 0x0100);
      assert s7.stack[3] == 0x279;
      var s8 := Exp(s7);
      assert s8.stack[2] == 0x279;
      var s9 := Swap(s8, 1);
      assert s9.stack[2] == 0x279;
      var s10 := Div(s9);
      assert s10.stack[1] == 0x279;
      var s11 := PushN(s10, 1, 0xff);
      assert s11.stack[2] == 0x279;
      var s12 := And(s11);
      assert s12.stack[1] == 0x279;
      var s13 := Dup(s12, 2);
      assert s13.stack[0] == 0x279;
      assert s13.stack[2] == 0x279;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s14, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 44
    * Starting at 0x279
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x279 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x279

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x279;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0x279;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x279;
      var s4 := Dup(s3, 1);
      assert s4.stack[3] == 0x279;
      var s5 := Dup(s4, 3);
      assert s5.stack[4] == 0x279;
      var s6 := PushN(s5, 1, 0xff);
      assert s6.stack[5] == 0x279;
      var s7 := And(s6);
      assert s7.stack[4] == 0x279;
      var s8 := PushN(s7, 1, 0xff);
      assert s8.stack[5] == 0x279;
      var s9 := And(s8);
      assert s9.stack[4] == 0x279;
      var s10 := Dup(s9, 2);
      assert s10.stack[5] == 0x279;
      var s11 := MStore(s10);
      assert s11.stack[3] == 0x279;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[4] == 0x279;
      var s13 := Add(s12);
      assert s13.stack[3] == 0x279;
      var s14 := Swap(s13, 2);
      assert s14.stack[3] == 0x279;
      var s15 := Pop(s14);
      assert s15.stack[2] == 0x279;
      var s16 := Pop(s15);
      assert s16.stack[1] == 0x279;
      var s17 := PushN(s16, 1, 0x40);
      assert s17.stack[2] == 0x279;
      var s18 := MLoad(s17);
      assert s18.stack[2] == 0x279;
      var s19 := Dup(s18, 1);
      assert s19.stack[3] == 0x279;
      var s20 := Swap(s19, 2);
      assert s20.stack[3] == 0x279;
      var s21 := Sub(s20);
      assert s21.stack[2] == 0x279;
      var s22 := Swap(s21, 1);
      assert s22.stack[2] == 0x279;
      var s23 := Return(s22);
      // Segment is terminal (Revert, Stop or Return)
      s23
  }

  /** Node 74
    * Segment Id for this node is: 37
    * Starting at 0x243
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x024e);
      assert s4.stack[0] == 0x24e;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s5, gas - 1)
      else
        ExecuteFromCFGNode_s75(s5, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 38
    * Starting at 0x24a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 76
    * Segment Id for this node is: 39
    * Starting at 0x24e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0264);
      assert s2.stack[0] == 0x264;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[1] == 0x264;
      var s4 := Dup(s3, 1);
      assert s4.stack[2] == 0x264;
      var s5 := Dup(s4, 1);
      assert s5.stack[3] == 0x264;
      var s6 := CallDataLoad(s5);
      assert s6.stack[3] == 0x264;
      var s7 := Swap(s6, 1);
      assert s7.stack[3] == 0x264;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[4] == 0x264;
      var s9 := Add(s8);
      assert s9.stack[3] == 0x264;
      var s10 := Swap(s9, 1);
      assert s10.stack[3] == 0x264;
      var s11 := Swap(s10, 2);
      assert s11.stack[3] == 0x264;
      var s12 := Swap(s11, 1);
      assert s12.stack[3] == 0x264;
      var s13 := Pop(s12);
      assert s13.stack[2] == 0x264;
      var s14 := Pop(s13);
      assert s14.stack[1] == 0x264;
      var s15 := PushN(s14, 2, 0x09d9);
      assert s15.stack[0] == 0x9d9;
      assert s15.stack[2] == 0x264;
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s16, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 98
    * Starting at 0x9d9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x264

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x264;
      var s2 := Dup(s1, 1);
      assert s2.stack[2] == 0x264;
      var s3 := PushN(s2, 1, 0x03);
      assert s3.stack[3] == 0x264;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[4] == 0x264;
      var s5 := Caller(s4);
      assert s5.stack[5] == 0x264;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x264;
      var s7 := And(s6);
      assert s7.stack[5] == 0x264;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[6] == 0x264;
      var s9 := And(s8);
      assert s9.stack[5] == 0x264;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x264;
      var s11 := MStore(s10);
      assert s11.stack[4] == 0x264;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[5] == 0x264;
      var s13 := Add(s12);
      assert s13.stack[4] == 0x264;
      var s14 := Swap(s13, 1);
      assert s14.stack[4] == 0x264;
      var s15 := Dup(s14, 2);
      assert s15.stack[5] == 0x264;
      var s16 := MStore(s15);
      assert s16.stack[3] == 0x264;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[4] == 0x264;
      var s18 := Add(s17);
      assert s18.stack[3] == 0x264;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[4] == 0x264;
      var s20 := Keccak256(s19);
      assert s20.stack[3] == 0x264;
      var s21 := SLoad(s20);
      assert s21.stack[3] == 0x264;
      var s22 := Lt(s21);
      assert s22.stack[2] == 0x264;
      var s23 := IsZero(s22);
      assert s23.stack[2] == 0x264;
      var s24 := IsZero(s23);
      assert s24.stack[2] == 0x264;
      var s25 := IsZero(s24);
      assert s25.stack[2] == 0x264;
      var s26 := PushN(s25, 2, 0x0a27);
      assert s26.stack[0] == 0xa27;
      assert s26.stack[3] == 0x264;
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s27, gas - 1)
      else
        ExecuteFromCFGNode_s78(s27, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 99
    * Starting at 0xa23
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x264

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[2] == 0x264;
      var s2 := Dup(s1, 1);
      assert s2.stack[3] == 0x264;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 79
    * Segment Id for this node is: 100
    * Starting at 0xa27
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x264

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x264;
      var s2 := Dup(s1, 1);
      assert s2.stack[2] == 0x264;
      var s3 := PushN(s2, 1, 0x03);
      assert s3.stack[3] == 0x264;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[4] == 0x264;
      var s5 := Caller(s4);
      assert s5.stack[5] == 0x264;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[6] == 0x264;
      var s7 := And(s6);
      assert s7.stack[5] == 0x264;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[6] == 0x264;
      var s9 := And(s8);
      assert s9.stack[5] == 0x264;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x264;
      var s11 := MStore(s10);
      assert s11.stack[4] == 0x264;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[5] == 0x264;
      var s13 := Add(s12);
      assert s13.stack[4] == 0x264;
      var s14 := Swap(s13, 1);
      assert s14.stack[4] == 0x264;
      var s15 := Dup(s14, 2);
      assert s15.stack[5] == 0x264;
      var s16 := MStore(s15);
      assert s16.stack[3] == 0x264;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[4] == 0x264;
      var s18 := Add(s17);
      assert s18.stack[3] == 0x264;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[4] == 0x264;
      var s20 := Keccak256(s19);
      assert s20.stack[3] == 0x264;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[4] == 0x264;
      var s22 := Dup(s21, 3);
      assert s22.stack[5] == 0x264;
      var s23 := Dup(s22, 3);
      assert s23.stack[6] == 0x264;
      var s24 := SLoad(s23);
      assert s24.stack[6] == 0x264;
      var s25 := Sub(s24);
      assert s25.stack[5] == 0x264;
      var s26 := Swap(s25, 3);
      assert s26.stack[5] == 0x264;
      var s27 := Pop(s26);
      assert s27.stack[4] == 0x264;
      var s28 := Pop(s27);
      assert s28.stack[3] == 0x264;
      var s29 := Dup(s28, 2);
      assert s29.stack[4] == 0x264;
      var s30 := Swap(s29, 1);
      assert s30.stack[4] == 0x264;
      var s31 := SStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s80(s31, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 101
    * Starting at 0xa74
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x264

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[1] == 0x264;
      var s2 := Caller(s1);
      assert s2.stack[2] == 0x264;
      var s3 := PushN(s2, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s3.stack[3] == 0x264;
      var s4 := And(s3);
      assert s4.stack[2] == 0x264;
      var s5 := PushN(s4, 2, 0x08fc);
      assert s5.stack[3] == 0x264;
      var s6 := Dup(s5, 3);
      assert s6.stack[4] == 0x264;
      var s7 := Swap(s6, 1);
      assert s7.stack[4] == 0x264;
      var s8 := Dup(s7, 2);
      assert s8.stack[5] == 0x264;
      var s9 := IsZero(s8);
      assert s9.stack[5] == 0x264;
      var s10 := Mul(s9);
      assert s10.stack[4] == 0x264;
      var s11 := Swap(s10, 1);
      assert s11.stack[4] == 0x264;
      var s12 := PushN(s11, 1, 0x40);
      assert s12.stack[5] == 0x264;
      var s13 := MLoad(s12);
      assert s13.stack[5] == 0x264;
      var s14 := PushN(s13, 1, 0x00);
      assert s14.stack[6] == 0x264;
      var s15 := PushN(s14, 1, 0x40);
      assert s15.stack[7] == 0x264;
      var s16 := MLoad(s15);
      assert s16.stack[7] == 0x264;
      var s17 := Dup(s16, 1);
      assert s17.stack[8] == 0x264;
      var s18 := Dup(s17, 4);
      assert s18.stack[9] == 0x264;
      var s19 := Sub(s18);
      assert s19.stack[8] == 0x264;
      var s20 := Dup(s19, 2);
      assert s20.stack[9] == 0x264;
      var s21 := Dup(s20, 6);
      assert s21.stack[10] == 0x264;
      var s22 := Dup(s21, 9);
      assert s22.stack[11] == 0x264;
      var s23 := Dup(s22, 9);
      assert s23.stack[12] == 0x264;
      var s24 := Call(s23);
      assert s24.stack[6] == 0x264;
      var s25 := Swap(s24, 4);
      assert s25.stack[6] == 0x264;
      var s26 := Pop(s25);
      assert s26.stack[5] == 0x264;
      var s27 := Pop(s26);
      assert s27.stack[4] == 0x264;
      var s28 := Pop(s27);
      assert s28.stack[3] == 0x264;
      var s29 := Pop(s28);
      assert s29.stack[2] == 0x264;
      var s30 := IsZero(s29);
      assert s30.stack[2] == 0x264;
      var s31 := IsZero(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s81(s31, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 102
    * Starting at 0xaac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x264

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0ab4);
      assert s1.stack[0] == 0xab4;
      assert s1.stack[3] == 0x264;
      var s2 := JumpI(s1);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s1.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s2, gas - 1)
      else
        ExecuteFromCFGNode_s82(s2, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 103
    * Starting at 0xab0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x264

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[2] == 0x264;
      var s2 := Dup(s1, 1);
      assert s2.stack[3] == 0x264;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 83
    * Segment Id for this node is: 104
    * Starting at 0xab4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x264

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x264;
      var s2 := Caller(s1);
      assert s2.stack[2] == 0x264;
      var s3 := PushN(s2, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s3.stack[3] == 0x264;
      var s4 := And(s3);
      assert s4.stack[2] == 0x264;
      var s5 := PushN(s4, 32, 0x7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65);
      assert s5.stack[3] == 0x264;
      var s6 := Dup(s5, 3);
      assert s6.stack[4] == 0x264;
      var s7 := PushN(s6, 1, 0x40);
      assert s7.stack[5] == 0x264;
      var s8 := MLoad(s7);
      assert s8.stack[5] == 0x264;
      var s9 := Dup(s8, 1);
      assert s9.stack[6] == 0x264;
      var s10 := Dup(s9, 3);
      assert s10.stack[7] == 0x264;
      var s11 := Dup(s10, 2);
      assert s11.stack[8] == 0x264;
      var s12 := MStore(s11);
      assert s12.stack[6] == 0x264;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[7] == 0x264;
      var s14 := Add(s13);
      assert s14.stack[6] == 0x264;
      var s15 := Swap(s14, 2);
      assert s15.stack[6] == 0x264;
      var s16 := Pop(s15);
      assert s16.stack[5] == 0x264;
      var s17 := Pop(s16);
      assert s17.stack[4] == 0x264;
      var s18 := PushN(s17, 1, 0x40);
      assert s18.stack[5] == 0x264;
      var s19 := MLoad(s18);
      assert s19.stack[5] == 0x264;
      var s20 := Dup(s19, 1);
      assert s20.stack[6] == 0x264;
      var s21 := Swap(s20, 2);
      assert s21.stack[6] == 0x264;
      var s22 := Sub(s21);
      assert s22.stack[5] == 0x264;
      var s23 := Swap(s22, 1);
      assert s23.stack[5] == 0x264;
      var s24 := LogN(s23, 2);
      assert s24.stack[1] == 0x264;
      var s25 := Pop(s24);
      assert s25.stack[0] == 0x264;
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s26, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 40
    * Starting at 0x264
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x264 as nat
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

  /** Node 85
    * Segment Id for this node is: 32
    * Starting at 0x1ca
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x01d5);
      assert s4.stack[0] == 0x1d5;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s5, gas - 1)
      else
        ExecuteFromCFGNode_s86(s5, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 33
    * Starting at 0x1d1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 87
    * Segment Id for this node is: 34
    * Starting at 0x1d5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0229);
      assert s2.stack[0] == 0x229;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[1] == 0x229;
      var s4 := Dup(s3, 1);
      assert s4.stack[2] == 0x229;
      var s5 := Dup(s4, 1);
      assert s5.stack[3] == 0x229;
      var s6 := CallDataLoad(s5);
      assert s6.stack[3] == 0x229;
      var s7 := PushN(s6, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s7.stack[4] == 0x229;
      var s8 := And(s7);
      assert s8.stack[3] == 0x229;
      var s9 := Swap(s8, 1);
      assert s9.stack[3] == 0x229;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[4] == 0x229;
      var s11 := Add(s10);
      assert s11.stack[3] == 0x229;
      var s12 := Swap(s11, 1);
      assert s12.stack[3] == 0x229;
      var s13 := Swap(s12, 2);
      assert s13.stack[3] == 0x229;
      var s14 := Swap(s13, 1);
      assert s14.stack[3] == 0x229;
      var s15 := Dup(s14, 1);
      assert s15.stack[4] == 0x229;
      var s16 := CallDataLoad(s15);
      assert s16.stack[4] == 0x229;
      var s17 := PushN(s16, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s17.stack[5] == 0x229;
      var s18 := And(s17);
      assert s18.stack[4] == 0x229;
      var s19 := Swap(s18, 1);
      assert s19.stack[4] == 0x229;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[5] == 0x229;
      var s21 := Add(s20);
      assert s21.stack[4] == 0x229;
      var s22 := Swap(s21, 1);
      assert s22.stack[4] == 0x229;
      var s23 := Swap(s22, 2);
      assert s23.stack[4] == 0x229;
      var s24 := Swap(s23, 1);
      assert s24.stack[4] == 0x229;
      var s25 := Dup(s24, 1);
      assert s25.stack[5] == 0x229;
      var s26 := CallDataLoad(s25);
      assert s26.stack[5] == 0x229;
      var s27 := Swap(s26, 1);
      assert s27.stack[5] == 0x229;
      var s28 := PushN(s27, 1, 0x20);
      assert s28.stack[6] == 0x229;
      var s29 := Add(s28);
      assert s29.stack[5] == 0x229;
      var s30 := Swap(s29, 1);
      assert s30.stack[5] == 0x229;
      var s31 := Swap(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s88(s31, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 35
    * Starting at 0x222
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[5] == 0x229;
      var s2 := Pop(s1);
      assert s2.stack[4] == 0x229;
      var s3 := Pop(s2);
      assert s3.stack[3] == 0x229;
      var s4 := PushN(s3, 2, 0x068c);
      assert s4.stack[0] == 0x68c;
      assert s4.stack[4] == 0x229;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s5, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 83
    * Starting at 0x68c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x229;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[4] == 0x229;
      var s3 := Dup(s2, 2);
      assert s3.stack[5] == 0x229;
      var s4 := PushN(s3, 1, 0x03);
      assert s4.stack[6] == 0x229;
      var s5 := PushN(s4, 1, 0x00);
      assert s5.stack[7] == 0x229;
      var s6 := Dup(s5, 7);
      assert s6.stack[8] == 0x229;
      var s7 := PushN(s6, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s7.stack[9] == 0x229;
      var s8 := And(s7);
      assert s8.stack[8] == 0x229;
      var s9 := PushN(s8, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s9.stack[9] == 0x229;
      var s10 := And(s9);
      assert s10.stack[8] == 0x229;
      var s11 := Dup(s10, 2);
      assert s11.stack[9] == 0x229;
      var s12 := MStore(s11);
      assert s12.stack[7] == 0x229;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[8] == 0x229;
      var s14 := Add(s13);
      assert s14.stack[7] == 0x229;
      var s15 := Swap(s14, 1);
      assert s15.stack[7] == 0x229;
      var s16 := Dup(s15, 2);
      assert s16.stack[8] == 0x229;
      var s17 := MStore(s16);
      assert s17.stack[6] == 0x229;
      var s18 := PushN(s17, 1, 0x20);
      assert s18.stack[7] == 0x229;
      var s19 := Add(s18);
      assert s19.stack[6] == 0x229;
      var s20 := PushN(s19, 1, 0x00);
      assert s20.stack[7] == 0x229;
      var s21 := Keccak256(s20);
      assert s21.stack[6] == 0x229;
      var s22 := SLoad(s21);
      assert s22.stack[6] == 0x229;
      var s23 := Lt(s22);
      assert s23.stack[5] == 0x229;
      var s24 := IsZero(s23);
      assert s24.stack[5] == 0x229;
      var s25 := IsZero(s24);
      assert s25.stack[5] == 0x229;
      var s26 := IsZero(s25);
      assert s26.stack[5] == 0x229;
      var s27 := PushN(s26, 2, 0x06dc);
      assert s27.stack[0] == 0x6dc;
      assert s27.stack[6] == 0x229;
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s91(s28, gas - 1)
      else
        ExecuteFromCFGNode_s90(s28, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 84
    * Starting at 0x6d8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x229;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x229;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 91
    * Segment Id for this node is: 85
    * Starting at 0x6dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x229;
      var s2 := Caller(s1);
      assert s2.stack[5] == 0x229;
      var s3 := PushN(s2, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s3.stack[6] == 0x229;
      var s4 := And(s3);
      assert s4.stack[5] == 0x229;
      var s5 := Dup(s4, 5);
      assert s5.stack[6] == 0x229;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[7] == 0x229;
      var s7 := And(s6);
      assert s7.stack[6] == 0x229;
      var s8 := Eq(s7);
      assert s8.stack[5] == 0x229;
      var s9 := IsZero(s8);
      assert s9.stack[5] == 0x229;
      var s10 := Dup(s9, 1);
      assert s10.stack[6] == 0x229;
      var s11 := IsZero(s10);
      assert s11.stack[6] == 0x229;
      var s12 := PushN(s11, 2, 0x07b4);
      assert s12.stack[0] == 0x7b4;
      assert s12.stack[7] == 0x229;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s13, gas - 1)
      else
        ExecuteFromCFGNode_s92(s13, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 86
    * Starting at 0x713
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x713 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[4] == 0x229;
      var s2 := PushN(s1, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      assert s2.stack[5] == 0x229;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[6] == 0x229;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[7] == 0x229;
      var s5 := Dup(s4, 7);
      assert s5.stack[8] == 0x229;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[9] == 0x229;
      var s7 := And(s6);
      assert s7.stack[8] == 0x229;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[9] == 0x229;
      var s9 := And(s8);
      assert s9.stack[8] == 0x229;
      var s10 := Dup(s9, 2);
      assert s10.stack[9] == 0x229;
      var s11 := MStore(s10);
      assert s11.stack[7] == 0x229;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[8] == 0x229;
      var s13 := Add(s12);
      assert s13.stack[7] == 0x229;
      var s14 := Swap(s13, 1);
      assert s14.stack[7] == 0x229;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0x229;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0x229;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0x229;
      var s18 := Add(s17);
      assert s18.stack[6] == 0x229;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[7] == 0x229;
      var s20 := Keccak256(s19);
      assert s20.stack[6] == 0x229;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[7] == 0x229;
      var s22 := Caller(s21);
      assert s22.stack[8] == 0x229;
      var s23 := PushN(s22, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s23.stack[9] == 0x229;
      var s24 := And(s23);
      assert s24.stack[8] == 0x229;
      var s25 := PushN(s24, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s25.stack[9] == 0x229;
      var s26 := And(s25);
      assert s26.stack[8] == 0x229;
      var s27 := Dup(s26, 2);
      assert s27.stack[9] == 0x229;
      var s28 := MStore(s27);
      assert s28.stack[7] == 0x229;
      var s29 := PushN(s28, 1, 0x20);
      assert s29.stack[8] == 0x229;
      var s30 := Add(s29);
      assert s30.stack[7] == 0x229;
      var s31 := Swap(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s93(s31, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 87
    * Starting at 0x7a9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[8] == 0x229;
      var s2 := MStore(s1);
      assert s2.stack[6] == 0x229;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[7] == 0x229;
      var s4 := Add(s3);
      assert s4.stack[6] == 0x229;
      var s5 := PushN(s4, 1, 0x00);
      assert s5.stack[7] == 0x229;
      var s6 := Keccak256(s5);
      assert s6.stack[6] == 0x229;
      var s7 := SLoad(s6);
      assert s7.stack[6] == 0x229;
      var s8 := Eq(s7);
      assert s8.stack[5] == 0x229;
      var s9 := IsZero(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s94(s9, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 88
    * Starting at 0x7b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x229;
      var s2 := IsZero(s1);
      assert s2.stack[5] == 0x229;
      var s3 := PushN(s2, 2, 0x08cf);
      assert s3.stack[0] == 0x8cf;
      assert s3.stack[6] == 0x229;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s4, gas - 1)
      else
        ExecuteFromCFGNode_s95(s4, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 89
    * Starting at 0x7ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[5] == 0x229;
      var s2 := PushN(s1, 1, 0x04);
      assert s2.stack[6] == 0x229;
      var s3 := PushN(s2, 1, 0x00);
      assert s3.stack[7] == 0x229;
      var s4 := Dup(s3, 7);
      assert s4.stack[8] == 0x229;
      var s5 := PushN(s4, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s5.stack[9] == 0x229;
      var s6 := And(s5);
      assert s6.stack[8] == 0x229;
      var s7 := PushN(s6, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s7.stack[9] == 0x229;
      var s8 := And(s7);
      assert s8.stack[8] == 0x229;
      var s9 := Dup(s8, 2);
      assert s9.stack[9] == 0x229;
      var s10 := MStore(s9);
      assert s10.stack[7] == 0x229;
      var s11 := PushN(s10, 1, 0x20);
      assert s11.stack[8] == 0x229;
      var s12 := Add(s11);
      assert s12.stack[7] == 0x229;
      var s13 := Swap(s12, 1);
      assert s13.stack[7] == 0x229;
      var s14 := Dup(s13, 2);
      assert s14.stack[8] == 0x229;
      var s15 := MStore(s14);
      assert s15.stack[6] == 0x229;
      var s16 := PushN(s15, 1, 0x20);
      assert s16.stack[7] == 0x229;
      var s17 := Add(s16);
      assert s17.stack[6] == 0x229;
      var s18 := PushN(s17, 1, 0x00);
      assert s18.stack[7] == 0x229;
      var s19 := Keccak256(s18);
      assert s19.stack[6] == 0x229;
      var s20 := PushN(s19, 1, 0x00);
      assert s20.stack[7] == 0x229;
      var s21 := Caller(s20);
      assert s21.stack[8] == 0x229;
      var s22 := PushN(s21, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s22.stack[9] == 0x229;
      var s23 := And(s22);
      assert s23.stack[8] == 0x229;
      var s24 := PushN(s23, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s24.stack[9] == 0x229;
      var s25 := And(s24);
      assert s25.stack[8] == 0x229;
      var s26 := Dup(s25, 2);
      assert s26.stack[9] == 0x229;
      var s27 := MStore(s26);
      assert s27.stack[7] == 0x229;
      var s28 := PushN(s27, 1, 0x20);
      assert s28.stack[8] == 0x229;
      var s29 := Add(s28);
      assert s29.stack[7] == 0x229;
      var s30 := Swap(s29, 1);
      assert s30.stack[7] == 0x229;
      var s31 := Dup(s30, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s96(s31, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 90
    * Starting at 0x830
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x830 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.stack[6] == 0x229;
      var s2 := PushN(s1, 1, 0x20);
      assert s2.stack[7] == 0x229;
      var s3 := Add(s2);
      assert s3.stack[6] == 0x229;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[7] == 0x229;
      var s5 := Keccak256(s4);
      assert s5.stack[6] == 0x229;
      var s6 := SLoad(s5);
      assert s6.stack[6] == 0x229;
      var s7 := Lt(s6);
      assert s7.stack[5] == 0x229;
      var s8 := IsZero(s7);
      assert s8.stack[5] == 0x229;
      var s9 := IsZero(s8);
      assert s9.stack[5] == 0x229;
      var s10 := IsZero(s9);
      assert s10.stack[5] == 0x229;
      var s11 := PushN(s10, 2, 0x0844);
      assert s11.stack[0] == 0x844;
      assert s11.stack[6] == 0x229;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s12, gas - 1)
      else
        ExecuteFromCFGNode_s97(s12, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 91
    * Starting at 0x840
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x840 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x229;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x229;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 98
    * Segment Id for this node is: 92
    * Starting at 0x844
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x844 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x229;
      var s2 := Dup(s1, 2);
      assert s2.stack[5] == 0x229;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[6] == 0x229;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[7] == 0x229;
      var s5 := Dup(s4, 7);
      assert s5.stack[8] == 0x229;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[9] == 0x229;
      var s7 := And(s6);
      assert s7.stack[8] == 0x229;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[9] == 0x229;
      var s9 := And(s8);
      assert s9.stack[8] == 0x229;
      var s10 := Dup(s9, 2);
      assert s10.stack[9] == 0x229;
      var s11 := MStore(s10);
      assert s11.stack[7] == 0x229;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[8] == 0x229;
      var s13 := Add(s12);
      assert s13.stack[7] == 0x229;
      var s14 := Swap(s13, 1);
      assert s14.stack[7] == 0x229;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0x229;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0x229;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0x229;
      var s18 := Add(s17);
      assert s18.stack[6] == 0x229;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[7] == 0x229;
      var s20 := Keccak256(s19);
      assert s20.stack[6] == 0x229;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[7] == 0x229;
      var s22 := Caller(s21);
      assert s22.stack[8] == 0x229;
      var s23 := PushN(s22, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s23.stack[9] == 0x229;
      var s24 := And(s23);
      assert s24.stack[8] == 0x229;
      var s25 := PushN(s24, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s25.stack[9] == 0x229;
      var s26 := And(s25);
      assert s26.stack[8] == 0x229;
      var s27 := Dup(s26, 2);
      assert s27.stack[9] == 0x229;
      var s28 := MStore(s27);
      assert s28.stack[7] == 0x229;
      var s29 := PushN(s28, 1, 0x20);
      assert s29.stack[8] == 0x229;
      var s30 := Add(s29);
      assert s30.stack[7] == 0x229;
      var s31 := Swap(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s99(s31, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 93
    * Starting at 0x8ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[8] == 0x229;
      var s2 := MStore(s1);
      assert s2.stack[6] == 0x229;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[7] == 0x229;
      var s4 := Add(s3);
      assert s4.stack[6] == 0x229;
      var s5 := PushN(s4, 1, 0x00);
      assert s5.stack[7] == 0x229;
      var s6 := Keccak256(s5);
      assert s6.stack[6] == 0x229;
      var s7 := PushN(s6, 1, 0x00);
      assert s7.stack[7] == 0x229;
      var s8 := Dup(s7, 3);
      assert s8.stack[8] == 0x229;
      var s9 := Dup(s8, 3);
      assert s9.stack[9] == 0x229;
      var s10 := SLoad(s9);
      assert s10.stack[9] == 0x229;
      var s11 := Sub(s10);
      assert s11.stack[8] == 0x229;
      var s12 := Swap(s11, 3);
      assert s12.stack[8] == 0x229;
      var s13 := Pop(s12);
      assert s13.stack[7] == 0x229;
      var s14 := Pop(s13);
      assert s14.stack[6] == 0x229;
      var s15 := Dup(s14, 2);
      assert s15.stack[7] == 0x229;
      var s16 := Swap(s15, 1);
      assert s16.stack[7] == 0x229;
      var s17 := SStore(s16);
      assert s17.stack[5] == 0x229;
      var s18 := Pop(s17);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s100(s18, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 94
    * Starting at 0x8cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x229;
      var s2 := Dup(s1, 2);
      assert s2.stack[5] == 0x229;
      var s3 := PushN(s2, 1, 0x03);
      assert s3.stack[6] == 0x229;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[7] == 0x229;
      var s5 := Dup(s4, 7);
      assert s5.stack[8] == 0x229;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[9] == 0x229;
      var s7 := And(s6);
      assert s7.stack[8] == 0x229;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[9] == 0x229;
      var s9 := And(s8);
      assert s9.stack[8] == 0x229;
      var s10 := Dup(s9, 2);
      assert s10.stack[9] == 0x229;
      var s11 := MStore(s10);
      assert s11.stack[7] == 0x229;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[8] == 0x229;
      var s13 := Add(s12);
      assert s13.stack[7] == 0x229;
      var s14 := Swap(s13, 1);
      assert s14.stack[7] == 0x229;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0x229;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0x229;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0x229;
      var s18 := Add(s17);
      assert s18.stack[6] == 0x229;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[7] == 0x229;
      var s20 := Keccak256(s19);
      assert s20.stack[6] == 0x229;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[7] == 0x229;
      var s22 := Dup(s21, 3);
      assert s22.stack[8] == 0x229;
      var s23 := Dup(s22, 3);
      assert s23.stack[9] == 0x229;
      var s24 := SLoad(s23);
      assert s24.stack[9] == 0x229;
      var s25 := Sub(s24);
      assert s25.stack[8] == 0x229;
      var s26 := Swap(s25, 3);
      assert s26.stack[8] == 0x229;
      var s27 := Pop(s26);
      assert s27.stack[7] == 0x229;
      var s28 := Pop(s27);
      assert s28.stack[6] == 0x229;
      var s29 := Dup(s28, 2);
      assert s29.stack[7] == 0x229;
      var s30 := Swap(s29, 1);
      assert s30.stack[7] == 0x229;
      var s31 := SStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s101(s31, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 95
    * Starting at 0x91c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[4] == 0x229;
      var s2 := Dup(s1, 2);
      assert s2.stack[5] == 0x229;
      var s3 := PushN(s2, 1, 0x03);
      assert s3.stack[6] == 0x229;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[7] == 0x229;
      var s5 := Dup(s4, 6);
      assert s5.stack[8] == 0x229;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[9] == 0x229;
      var s7 := And(s6);
      assert s7.stack[8] == 0x229;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[9] == 0x229;
      var s9 := And(s8);
      assert s9.stack[8] == 0x229;
      var s10 := Dup(s9, 2);
      assert s10.stack[9] == 0x229;
      var s11 := MStore(s10);
      assert s11.stack[7] == 0x229;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[8] == 0x229;
      var s13 := Add(s12);
      assert s13.stack[7] == 0x229;
      var s14 := Swap(s13, 1);
      assert s14.stack[7] == 0x229;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0x229;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0x229;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0x229;
      var s18 := Add(s17);
      assert s18.stack[6] == 0x229;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[7] == 0x229;
      var s20 := Keccak256(s19);
      assert s20.stack[6] == 0x229;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[7] == 0x229;
      var s22 := Dup(s21, 3);
      assert s22.stack[8] == 0x229;
      var s23 := Dup(s22, 3);
      assert s23.stack[9] == 0x229;
      var s24 := SLoad(s23);
      assert s24.stack[9] == 0x229;
      var s25 := Add(s24);
      assert s25.stack[8] == 0x229;
      var s26 := Swap(s25, 3);
      assert s26.stack[8] == 0x229;
      var s27 := Pop(s26);
      assert s27.stack[7] == 0x229;
      var s28 := Pop(s27);
      assert s28.stack[6] == 0x229;
      var s29 := Dup(s28, 2);
      assert s29.stack[7] == 0x229;
      var s30 := Swap(s29, 1);
      assert s30.stack[7] == 0x229;
      var s31 := SStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s102(s31, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 96
    * Starting at 0x969
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x969 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[4] == 0x229;
      var s2 := Dup(s1, 3);
      assert s2.stack[5] == 0x229;
      var s3 := PushN(s2, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s3.stack[6] == 0x229;
      var s4 := And(s3);
      assert s4.stack[5] == 0x229;
      var s5 := Dup(s4, 5);
      assert s5.stack[6] == 0x229;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[7] == 0x229;
      var s7 := And(s6);
      assert s7.stack[6] == 0x229;
      var s8 := PushN(s7, 32, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      assert s8.stack[7] == 0x229;
      var s9 := Dup(s8, 5);
      assert s9.stack[8] == 0x229;
      var s10 := PushN(s9, 1, 0x40);
      assert s10.stack[9] == 0x229;
      var s11 := MLoad(s10);
      assert s11.stack[9] == 0x229;
      var s12 := Dup(s11, 1);
      assert s12.stack[10] == 0x229;
      var s13 := Dup(s12, 3);
      assert s13.stack[11] == 0x229;
      var s14 := Dup(s13, 2);
      assert s14.stack[12] == 0x229;
      var s15 := MStore(s14);
      assert s15.stack[10] == 0x229;
      var s16 := PushN(s15, 1, 0x20);
      assert s16.stack[11] == 0x229;
      var s17 := Add(s16);
      assert s17.stack[10] == 0x229;
      var s18 := Swap(s17, 2);
      assert s18.stack[10] == 0x229;
      var s19 := Pop(s18);
      assert s19.stack[9] == 0x229;
      var s20 := Pop(s19);
      assert s20.stack[8] == 0x229;
      var s21 := PushN(s20, 1, 0x40);
      assert s21.stack[9] == 0x229;
      var s22 := MLoad(s21);
      assert s22.stack[9] == 0x229;
      var s23 := Dup(s22, 1);
      assert s23.stack[10] == 0x229;
      var s24 := Swap(s23, 2);
      assert s24.stack[10] == 0x229;
      var s25 := Sub(s24);
      assert s25.stack[9] == 0x229;
      var s26 := Swap(s25, 1);
      assert s26.stack[9] == 0x229;
      var s27 := LogN(s26, 3);
      assert s27.stack[4] == 0x229;
      var s28 := PushN(s27, 1, 0x01);
      assert s28.stack[5] == 0x229;
      var s29 := Swap(s28, 1);
      assert s29.stack[5] == 0x229;
      var s30 := Pop(s29);
      assert s30.stack[4] == 0x229;
      var s31 := Swap(s30, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s103(s31, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 97
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x229

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[3] == 0x229;
      var s2 := Pop(s1);
      assert s2.stack[2] == 0x229;
      var s3 := Pop(s2);
      assert s3.stack[1] == 0x229;
      var s4 := Pop(s3);
      assert s4.stack[0] == 0x229;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s5, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 36
    * Starting at 0x229
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x229 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := IsZero(s5);
      var s7 := IsZero(s6);
      var s8 := IsZero(s7);
      var s9 := IsZero(s8);
      var s10 := Dup(s9, 2);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Add(s12);
      var s14 := Swap(s13, 2);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := PushN(s16, 1, 0x40);
      var s18 := MLoad(s17);
      var s19 := Dup(s18, 1);
      var s20 := Swap(s19, 2);
      var s21 := Sub(s20);
      var s22 := Swap(s21, 1);
      var s23 := Return(s22);
      // Segment is terminal (Revert, Stop or Return)
      s23
  }

  /** Node 105
    * Segment Id for this node is: 28
    * Starting at 0x1a1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x01ac);
      assert s4.stack[0] == 0x1ac;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s5, gas - 1)
      else
        ExecuteFromCFGNode_s106(s5, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 29
    * Starting at 0x1a8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 107
    * Segment Id for this node is: 30
    * Starting at 0x1ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x01b4);
      assert s2.stack[0] == 0x1b4;
      var s3 := PushN(s2, 2, 0x066d);
      assert s3.stack[0] == 0x66d;
      assert s3.stack[1] == 0x1b4;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s4, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 82
    * Starting at 0x66d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1b4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0x1b4;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[1] == 0x1b4;
      var s3 := Address(s2);
      assert s3.stack[2] == 0x1b4;
      var s4 := PushN(s3, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s4.stack[3] == 0x1b4;
      var s5 := And(s4);
      assert s5.stack[2] == 0x1b4;
      var s6 := Balance(s5);
      assert s6.stack[2] == 0x1b4;
      var s7 := Swap(s6, 1);
      assert s7.stack[2] == 0x1b4;
      var s8 := Pop(s7);
      assert s8.stack[1] == 0x1b4;
      var s9 := Swap(s8, 1);
      assert s9.stack[0] == 0x1b4;
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s10, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 31
    * Starting at 0x1b4
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 1, 0x20);
      var s9 := Add(s8);
      var s10 := Swap(s9, 2);
      var s11 := Pop(s10);
      var s12 := Pop(s11);
      var s13 := PushN(s12, 1, 0x40);
      var s14 := MLoad(s13);
      var s15 := Dup(s14, 1);
      var s16 := Swap(s15, 2);
      var s17 := Sub(s16);
      var s18 := Swap(s17, 1);
      var s19 := Return(s18);
      // Segment is terminal (Revert, Stop or Return)
      s19
  }

  /** Node 110
    * Segment Id for this node is: 24
    * Starting at 0x147
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x147 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x0152);
      assert s4.stack[0] == 0x152;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s112(s5, gas - 1)
      else
        ExecuteFromCFGNode_s111(s5, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 25
    * Starting at 0x14e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 112
    * Segment Id for this node is: 26
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0187);
      assert s2.stack[0] == 0x187;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[1] == 0x187;
      var s4 := Dup(s3, 1);
      assert s4.stack[2] == 0x187;
      var s5 := Dup(s4, 1);
      assert s5.stack[3] == 0x187;
      var s6 := CallDataLoad(s5);
      assert s6.stack[3] == 0x187;
      var s7 := PushN(s6, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s7.stack[4] == 0x187;
      var s8 := And(s7);
      assert s8.stack[3] == 0x187;
      var s9 := Swap(s8, 1);
      assert s9.stack[3] == 0x187;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[4] == 0x187;
      var s11 := Add(s10);
      assert s11.stack[3] == 0x187;
      var s12 := Swap(s11, 1);
      assert s12.stack[3] == 0x187;
      var s13 := Swap(s12, 2);
      assert s13.stack[3] == 0x187;
      var s14 := Swap(s13, 1);
      assert s14.stack[3] == 0x187;
      var s15 := Dup(s14, 1);
      assert s15.stack[4] == 0x187;
      var s16 := CallDataLoad(s15);
      assert s16.stack[4] == 0x187;
      var s17 := Swap(s16, 1);
      assert s17.stack[4] == 0x187;
      var s18 := PushN(s17, 1, 0x20);
      assert s18.stack[5] == 0x187;
      var s19 := Add(s18);
      assert s19.stack[4] == 0x187;
      var s20 := Swap(s19, 1);
      assert s20.stack[4] == 0x187;
      var s21 := Swap(s20, 2);
      assert s21.stack[4] == 0x187;
      var s22 := Swap(s21, 1);
      assert s22.stack[4] == 0x187;
      var s23 := Pop(s22);
      assert s23.stack[3] == 0x187;
      var s24 := Pop(s23);
      assert s24.stack[2] == 0x187;
      var s25 := PushN(s24, 2, 0x057b);
      assert s25.stack[0] == 0x57b;
      assert s25.stack[3] == 0x187;
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s26, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 79
    * Starting at 0x57b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x187

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x187;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[3] == 0x187;
      var s3 := Dup(s2, 2);
      assert s3.stack[4] == 0x187;
      var s4 := PushN(s3, 1, 0x04);
      assert s4.stack[5] == 0x187;
      var s5 := PushN(s4, 1, 0x00);
      assert s5.stack[6] == 0x187;
      var s6 := Caller(s5);
      assert s6.stack[7] == 0x187;
      var s7 := PushN(s6, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s7.stack[8] == 0x187;
      var s8 := And(s7);
      assert s8.stack[7] == 0x187;
      var s9 := PushN(s8, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s9.stack[8] == 0x187;
      var s10 := And(s9);
      assert s10.stack[7] == 0x187;
      var s11 := Dup(s10, 2);
      assert s11.stack[8] == 0x187;
      var s12 := MStore(s11);
      assert s12.stack[6] == 0x187;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[7] == 0x187;
      var s14 := Add(s13);
      assert s14.stack[6] == 0x187;
      var s15 := Swap(s14, 1);
      assert s15.stack[6] == 0x187;
      var s16 := Dup(s15, 2);
      assert s16.stack[7] == 0x187;
      var s17 := MStore(s16);
      assert s17.stack[5] == 0x187;
      var s18 := PushN(s17, 1, 0x20);
      assert s18.stack[6] == 0x187;
      var s19 := Add(s18);
      assert s19.stack[5] == 0x187;
      var s20 := PushN(s19, 1, 0x00);
      assert s20.stack[6] == 0x187;
      var s21 := Keccak256(s20);
      assert s21.stack[5] == 0x187;
      var s22 := PushN(s21, 1, 0x00);
      assert s22.stack[6] == 0x187;
      var s23 := Dup(s22, 6);
      assert s23.stack[7] == 0x187;
      var s24 := PushN(s23, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s24.stack[8] == 0x187;
      var s25 := And(s24);
      assert s25.stack[7] == 0x187;
      var s26 := PushN(s25, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s26.stack[8] == 0x187;
      var s27 := And(s26);
      assert s27.stack[7] == 0x187;
      var s28 := Dup(s27, 2);
      assert s28.stack[8] == 0x187;
      var s29 := MStore(s28);
      assert s29.stack[6] == 0x187;
      var s30 := PushN(s29, 1, 0x20);
      assert s30.stack[7] == 0x187;
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s114(s31, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 80
    * Starting at 0x5f2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x187

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[6] == 0x187;
      var s2 := Dup(s1, 2);
      assert s2.stack[7] == 0x187;
      var s3 := MStore(s2);
      assert s3.stack[5] == 0x187;
      var s4 := PushN(s3, 1, 0x20);
      assert s4.stack[6] == 0x187;
      var s5 := Add(s4);
      assert s5.stack[5] == 0x187;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[6] == 0x187;
      var s7 := Keccak256(s6);
      assert s7.stack[5] == 0x187;
      var s8 := Dup(s7, 2);
      assert s8.stack[6] == 0x187;
      var s9 := Swap(s8, 1);
      assert s9.stack[6] == 0x187;
      var s10 := SStore(s9);
      assert s10.stack[4] == 0x187;
      var s11 := Pop(s10);
      assert s11.stack[3] == 0x187;
      var s12 := Dup(s11, 3);
      assert s12.stack[4] == 0x187;
      var s13 := PushN(s12, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s13.stack[5] == 0x187;
      var s14 := And(s13);
      assert s14.stack[4] == 0x187;
      var s15 := Caller(s14);
      assert s15.stack[5] == 0x187;
      var s16 := PushN(s15, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s16.stack[6] == 0x187;
      var s17 := And(s16);
      assert s17.stack[5] == 0x187;
      var s18 := PushN(s17, 32, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      assert s18.stack[6] == 0x187;
      var s19 := Dup(s18, 5);
      assert s19.stack[7] == 0x187;
      var s20 := PushN(s19, 1, 0x40);
      assert s20.stack[8] == 0x187;
      var s21 := MLoad(s20);
      assert s21.stack[8] == 0x187;
      var s22 := Dup(s21, 1);
      assert s22.stack[9] == 0x187;
      var s23 := Dup(s22, 3);
      assert s23.stack[10] == 0x187;
      var s24 := Dup(s23, 2);
      assert s24.stack[11] == 0x187;
      var s25 := MStore(s24);
      assert s25.stack[9] == 0x187;
      var s26 := PushN(s25, 1, 0x20);
      assert s26.stack[10] == 0x187;
      var s27 := Add(s26);
      assert s27.stack[9] == 0x187;
      var s28 := Swap(s27, 2);
      assert s28.stack[9] == 0x187;
      var s29 := Pop(s28);
      assert s29.stack[8] == 0x187;
      var s30 := Pop(s29);
      assert s30.stack[7] == 0x187;
      var s31 := PushN(s30, 1, 0x40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s115(s31, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 81
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x187

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MLoad(s0);
      assert s1.stack[8] == 0x187;
      var s2 := Dup(s1, 1);
      assert s2.stack[9] == 0x187;
      var s3 := Swap(s2, 2);
      assert s3.stack[9] == 0x187;
      var s4 := Sub(s3);
      assert s4.stack[8] == 0x187;
      var s5 := Swap(s4, 1);
      assert s5.stack[8] == 0x187;
      var s6 := LogN(s5, 3);
      assert s6.stack[3] == 0x187;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[4] == 0x187;
      var s8 := Swap(s7, 1);
      assert s8.stack[4] == 0x187;
      var s9 := Pop(s8);
      assert s9.stack[3] == 0x187;
      var s10 := Swap(s9, 3);
      assert s10.stack[0] == 0x187;
      var s11 := Swap(s10, 2);
      assert s11.stack[2] == 0x187;
      var s12 := Pop(s11);
      assert s12.stack[1] == 0x187;
      var s13 := Pop(s12);
      assert s13.stack[0] == 0x187;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s14, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 27
    * Starting at 0x187
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x187 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup(s3, 1);
      var s5 := Dup(s4, 3);
      var s6 := IsZero(s5);
      var s7 := IsZero(s6);
      var s8 := IsZero(s7);
      var s9 := IsZero(s8);
      var s10 := Dup(s9, 2);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Add(s12);
      var s14 := Swap(s13, 2);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := PushN(s16, 1, 0x40);
      var s18 := MLoad(s17);
      var s19 := Dup(s18, 1);
      var s20 := Swap(s19, 2);
      var s21 := Sub(s20);
      var s22 := Swap(s21, 1);
      var s23 := Return(s22);
      // Segment is terminal (Revert, Stop or Return)
      s23
  }

  /** Node 117
    * Segment Id for this node is: 14
    * Starting at 0xb9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x00c4);
      assert s4.stack[0] == 0xc4;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s119(s5, gas - 1)
      else
        ExecuteFromCFGNode_s118(s5, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 15
    * Starting at 0xc0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 119
    * Segment Id for this node is: 16
    * Starting at 0xc4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x00cc);
      assert s2.stack[0] == 0xcc;
      var s3 := PushN(s2, 2, 0x04dd);
      assert s3.stack[0] == 0x4dd;
      assert s3.stack[1] == 0xcc;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s4, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 71
    * Starting at 0x4dd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0xcc;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[1] == 0xcc;
      var s3 := Dup(s2, 1);
      assert s3.stack[2] == 0xcc;
      var s4 := SLoad(s3);
      assert s4.stack[2] == 0xcc;
      var s5 := PushN(s4, 1, 0x01);
      assert s5.stack[3] == 0xcc;
      var s6 := Dup(s5, 2);
      assert s6.stack[4] == 0xcc;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[5] == 0xcc;
      var s8 := And(s7);
      assert s8.stack[4] == 0xcc;
      var s9 := IsZero(s8);
      assert s9.stack[4] == 0xcc;
      var s10 := PushN(s9, 2, 0x0100);
      assert s10.stack[5] == 0xcc;
      var s11 := Mul(s10);
      assert s11.stack[4] == 0xcc;
      var s12 := Sub(s11);
      assert s12.stack[3] == 0xcc;
      var s13 := And(s12);
      assert s13.stack[2] == 0xcc;
      var s14 := PushN(s13, 1, 0x02);
      assert s14.stack[3] == 0xcc;
      var s15 := Swap(s14, 1);
      assert s15.stack[3] == 0xcc;
      var s16 := Div(s15);
      assert s16.stack[2] == 0xcc;
      var s17 := Dup(s16, 1);
      assert s17.stack[3] == 0xcc;
      var s18 := PushN(s17, 1, 0x1f);
      assert s18.stack[4] == 0xcc;
      var s19 := Add(s18);
      assert s19.stack[3] == 0xcc;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[4] == 0xcc;
      var s21 := Dup(s20, 1);
      assert s21.stack[5] == 0xcc;
      var s22 := Swap(s21, 2);
      assert s22.stack[5] == 0xcc;
      var s23 := Div(s22);
      assert s23.stack[4] == 0xcc;
      var s24 := Mul(s23);
      assert s24.stack[3] == 0xcc;
      var s25 := PushN(s24, 1, 0x20);
      assert s25.stack[4] == 0xcc;
      var s26 := Add(s25);
      assert s26.stack[3] == 0xcc;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[4] == 0xcc;
      var s28 := MLoad(s27);
      assert s28.stack[4] == 0xcc;
      var s29 := Swap(s28, 1);
      assert s29.stack[4] == 0xcc;
      var s30 := Dup(s29, 2);
      assert s30.stack[5] == 0xcc;
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s121(s31, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 72
    * Starting at 0x506
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x506 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[5] == 0xcc;
      var s2 := MStore(s1);
      assert s2.stack[3] == 0xcc;
      var s3 := Dup(s2, 1);
      assert s3.stack[4] == 0xcc;
      var s4 := Swap(s3, 3);
      assert s4.stack[4] == 0xcc;
      var s5 := Swap(s4, 2);
      assert s5.stack[4] == 0xcc;
      var s6 := Swap(s5, 1);
      assert s6.stack[4] == 0xcc;
      var s7 := Dup(s6, 2);
      assert s7.stack[5] == 0xcc;
      var s8 := Dup(s7, 2);
      assert s8.stack[6] == 0xcc;
      var s9 := MStore(s8);
      assert s9.stack[4] == 0xcc;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[5] == 0xcc;
      var s11 := Add(s10);
      assert s11.stack[4] == 0xcc;
      var s12 := Dup(s11, 3);
      assert s12.stack[5] == 0xcc;
      var s13 := Dup(s12, 1);
      assert s13.stack[6] == 0xcc;
      var s14 := SLoad(s13);
      assert s14.stack[6] == 0xcc;
      var s15 := PushN(s14, 1, 0x01);
      assert s15.stack[7] == 0xcc;
      var s16 := Dup(s15, 2);
      assert s16.stack[8] == 0xcc;
      var s17 := PushN(s16, 1, 0x01);
      assert s17.stack[9] == 0xcc;
      var s18 := And(s17);
      assert s18.stack[8] == 0xcc;
      var s19 := IsZero(s18);
      assert s19.stack[8] == 0xcc;
      var s20 := PushN(s19, 2, 0x0100);
      assert s20.stack[9] == 0xcc;
      var s21 := Mul(s20);
      assert s21.stack[8] == 0xcc;
      var s22 := Sub(s21);
      assert s22.stack[7] == 0xcc;
      var s23 := And(s22);
      assert s23.stack[6] == 0xcc;
      var s24 := PushN(s23, 1, 0x02);
      assert s24.stack[7] == 0xcc;
      var s25 := Swap(s24, 1);
      assert s25.stack[7] == 0xcc;
      var s26 := Div(s25);
      assert s26.stack[6] == 0xcc;
      var s27 := Dup(s26, 1);
      assert s27.stack[7] == 0xcc;
      var s28 := IsZero(s27);
      assert s28.stack[7] == 0xcc;
      var s29 := PushN(s28, 2, 0x0573);
      assert s29.stack[0] == 0x573;
      assert s29.stack[8] == 0xcc;
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s124(s30, gas - 1)
      else
        ExecuteFromCFGNode_s122(s30, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 73
    * Starting at 0x52d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[7] == 0xcc;
      var s2 := PushN(s1, 1, 0x1f);
      assert s2.stack[8] == 0xcc;
      var s3 := Lt(s2);
      assert s3.stack[7] == 0xcc;
      var s4 := PushN(s3, 2, 0x0548);
      assert s4.stack[0] == 0x548;
      assert s4.stack[8] == 0xcc;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s5, gas - 1)
      else
        ExecuteFromCFGNode_s123(s5, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 74
    * Starting at 0x535
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x535 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      assert s1.stack[7] == 0xcc;
      var s2 := Dup(s1, 1);
      assert s2.stack[8] == 0xcc;
      var s3 := Dup(s2, 4);
      assert s3.stack[9] == 0xcc;
      var s4 := SLoad(s3);
      assert s4.stack[9] == 0xcc;
      var s5 := Div(s4);
      assert s5.stack[8] == 0xcc;
      var s6 := Mul(s5);
      assert s6.stack[7] == 0xcc;
      var s7 := Dup(s6, 4);
      assert s7.stack[8] == 0xcc;
      var s8 := MStore(s7);
      assert s8.stack[6] == 0xcc;
      var s9 := Swap(s8, 2);
      assert s9.stack[6] == 0xcc;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[7] == 0xcc;
      var s11 := Add(s10);
      assert s11.stack[6] == 0xcc;
      var s12 := Swap(s11, 2);
      assert s12.stack[6] == 0xcc;
      var s13 := PushN(s12, 2, 0x0573);
      assert s13.stack[0] == 0x573;
      assert s13.stack[7] == 0xcc;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s14, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 78
    * Starting at 0x573
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x573 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0xcc;
      var s2 := Pop(s1);
      assert s2.stack[5] == 0xcc;
      var s3 := Pop(s2);
      assert s3.stack[4] == 0xcc;
      var s4 := Pop(s3);
      assert s4.stack[3] == 0xcc;
      var s5 := Pop(s4);
      assert s5.stack[2] == 0xcc;
      var s6 := Pop(s5);
      assert s6.stack[1] == 0xcc;
      var s7 := Dup(s6, 2);
      assert s7.stack[0] == 0xcc;
      assert s7.stack[2] == 0xcc;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s8, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 17
    * Starting at 0xcc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0xcc;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0xcc;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0xcc;
      var s4 := Dup(s3, 1);
      assert s4.stack[3] == 0xcc;
      var s5 := Dup(s4, 1);
      assert s5.stack[4] == 0xcc;
      var s6 := PushN(s5, 1, 0x20);
      assert s6.stack[5] == 0xcc;
      var s7 := Add(s6);
      assert s7.stack[4] == 0xcc;
      var s8 := Dup(s7, 3);
      assert s8.stack[5] == 0xcc;
      var s9 := Dup(s8, 2);
      assert s9.stack[6] == 0xcc;
      var s10 := Sub(s9);
      assert s10.stack[5] == 0xcc;
      var s11 := Dup(s10, 3);
      assert s11.stack[6] == 0xcc;
      var s12 := MStore(s11);
      assert s12.stack[4] == 0xcc;
      var s13 := Dup(s12, 4);
      assert s13.stack[5] == 0xcc;
      var s14 := Dup(s13, 2);
      assert s14.stack[6] == 0xcc;
      var s15 := Dup(s14, 2);
      assert s15.stack[7] == 0xcc;
      var s16 := MLoad(s15);
      assert s16.stack[7] == 0xcc;
      var s17 := Dup(s16, 2);
      assert s17.stack[8] == 0xcc;
      var s18 := MStore(s17);
      assert s18.stack[6] == 0xcc;
      var s19 := PushN(s18, 1, 0x20);
      assert s19.stack[7] == 0xcc;
      var s20 := Add(s19);
      assert s20.stack[6] == 0xcc;
      var s21 := Swap(s20, 2);
      assert s21.stack[6] == 0xcc;
      var s22 := Pop(s21);
      assert s22.stack[5] == 0xcc;
      var s23 := Dup(s22, 1);
      assert s23.stack[6] == 0xcc;
      var s24 := MLoad(s23);
      assert s24.stack[6] == 0xcc;
      var s25 := Swap(s24, 1);
      assert s25.stack[6] == 0xcc;
      var s26 := PushN(s25, 1, 0x20);
      assert s26.stack[7] == 0xcc;
      var s27 := Add(s26);
      assert s27.stack[6] == 0xcc;
      var s28 := Swap(s27, 1);
      assert s28.stack[6] == 0xcc;
      var s29 := Dup(s28, 1);
      assert s29.stack[7] == 0xcc;
      var s30 := Dup(s29, 4);
      assert s30.stack[8] == 0xcc;
      var s31 := Dup(s30, 4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s126(s31, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 18
    * Starting at 0xef
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s127(s1, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 19
    * Starting at 0xf1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[10] == 0xcc;
      var s2 := Dup(s1, 4);
      assert s2.stack[11] == 0xcc;
      var s3 := Dup(s2, 2);
      assert s3.stack[12] == 0xcc;
      var s4 := Lt(s3);
      assert s4.stack[11] == 0xcc;
      var s5 := IsZero(s4);
      assert s5.stack[11] == 0xcc;
      var s6 := PushN(s5, 2, 0x010c);
      assert s6.stack[0] == 0x10c;
      assert s6.stack[12] == 0xcc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s129(s7, gas - 1)
      else
        ExecuteFromCFGNode_s128(s7, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 20
    * Starting at 0xfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[11] == 0xcc;
      var s2 := Dup(s1, 3);
      assert s2.stack[12] == 0xcc;
      var s3 := Add(s2);
      assert s3.stack[11] == 0xcc;
      var s4 := MLoad(s3);
      assert s4.stack[11] == 0xcc;
      var s5 := Dup(s4, 2);
      assert s5.stack[12] == 0xcc;
      var s6 := Dup(s5, 5);
      assert s6.stack[13] == 0xcc;
      var s7 := Add(s6);
      assert s7.stack[12] == 0xcc;
      var s8 := MStore(s7);
      assert s8.stack[10] == 0xcc;
      var s9 := PushN(s8, 1, 0x20);
      assert s9.stack[11] == 0xcc;
      var s10 := Dup(s9, 2);
      assert s10.stack[12] == 0xcc;
      var s11 := Add(s10);
      assert s11.stack[11] == 0xcc;
      var s12 := Swap(s11, 1);
      assert s12.stack[11] == 0xcc;
      var s13 := Pop(s12);
      assert s13.stack[10] == 0xcc;
      var s14 := PushN(s13, 2, 0x00f1);
      assert s14.stack[0] == 0xf1;
      assert s14.stack[11] == 0xcc;
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s15, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 21
    * Starting at 0x10c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[10] == 0xcc;
      var s2 := Pop(s1);
      assert s2.stack[9] == 0xcc;
      var s3 := Pop(s2);
      assert s3.stack[8] == 0xcc;
      var s4 := Pop(s3);
      assert s4.stack[7] == 0xcc;
      var s5 := Pop(s4);
      assert s5.stack[6] == 0xcc;
      var s6 := Swap(s5, 1);
      assert s6.stack[6] == 0xcc;
      var s7 := Pop(s6);
      assert s7.stack[5] == 0xcc;
      var s8 := Swap(s7, 1);
      assert s8.stack[5] == 0xcc;
      var s9 := Dup(s8, 2);
      assert s9.stack[6] == 0xcc;
      var s10 := Add(s9);
      assert s10.stack[5] == 0xcc;
      var s11 := Swap(s10, 1);
      assert s11.stack[5] == 0xcc;
      var s12 := PushN(s11, 1, 0x1f);
      assert s12.stack[6] == 0xcc;
      var s13 := And(s12);
      assert s13.stack[5] == 0xcc;
      var s14 := Dup(s13, 1);
      assert s14.stack[6] == 0xcc;
      var s15 := IsZero(s14);
      assert s15.stack[6] == 0xcc;
      var s16 := PushN(s15, 2, 0x0139);
      assert s16.stack[0] == 0x139;
      assert s16.stack[7] == 0xcc;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s17, gas - 1)
      else
        ExecuteFromCFGNode_s130(s17, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 22
    * Starting at 0x120
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[6] == 0xcc;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0xcc;
      var s3 := Sub(s2);
      assert s3.stack[6] == 0xcc;
      var s4 := Dup(s3, 1);
      assert s4.stack[7] == 0xcc;
      var s5 := MLoad(s4);
      assert s5.stack[7] == 0xcc;
      var s6 := PushN(s5, 1, 0x01);
      assert s6.stack[8] == 0xcc;
      var s7 := Dup(s6, 4);
      assert s7.stack[9] == 0xcc;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[10] == 0xcc;
      var s9 := Sub(s8);
      assert s9.stack[9] == 0xcc;
      var s10 := PushN(s9, 2, 0x0100);
      assert s10.stack[10] == 0xcc;
      var s11 := Exp(s10);
      assert s11.stack[9] == 0xcc;
      var s12 := Sub(s11);
      assert s12.stack[8] == 0xcc;
      var s13 := Not(s12);
      assert s13.stack[8] == 0xcc;
      var s14 := And(s13);
      assert s14.stack[7] == 0xcc;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0xcc;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0xcc;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0xcc;
      var s18 := Add(s17);
      assert s18.stack[6] == 0xcc;
      var s19 := Swap(s18, 2);
      assert s19.stack[6] == 0xcc;
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s131(s20, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 23
    * Starting at 0x139
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0xcc;
      var s2 := Pop(s1);
      assert s2.stack[4] == 0xcc;
      var s3 := Swap(s2, 3);
      assert s3.stack[4] == 0xcc;
      var s4 := Pop(s3);
      assert s4.stack[3] == 0xcc;
      var s5 := Pop(s4);
      assert s5.stack[2] == 0xcc;
      var s6 := Pop(s5);
      assert s6.stack[1] == 0xcc;
      var s7 := PushN(s6, 1, 0x40);
      assert s7.stack[2] == 0xcc;
      var s8 := MLoad(s7);
      assert s8.stack[2] == 0xcc;
      var s9 := Dup(s8, 1);
      assert s9.stack[3] == 0xcc;
      var s10 := Swap(s9, 2);
      assert s10.stack[3] == 0xcc;
      var s11 := Sub(s10);
      assert s11.stack[2] == 0xcc;
      var s12 := Swap(s11, 1);
      assert s12.stack[2] == 0xcc;
      var s13 := Return(s12);
      // Segment is terminal (Revert, Stop or Return)
      s13
  }

  /** Node 132
    * Segment Id for this node is: 75
    * Starting at 0x548
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x548 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0xcc;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0xcc;
      var s3 := Add(s2);
      assert s3.stack[6] == 0xcc;
      var s4 := Swap(s3, 2);
      assert s4.stack[6] == 0xcc;
      var s5 := Swap(s4, 1);
      assert s5.stack[6] == 0xcc;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[7] == 0xcc;
      var s7 := MStore(s6);
      assert s7.stack[5] == 0xcc;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[6] == 0xcc;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[7] == 0xcc;
      var s10 := Keccak256(s9);
      assert s10.stack[6] == 0xcc;
      var s11 := Swap(s10, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s133(s11, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 76
    * Starting at 0x556
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x556 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0xcc;
      var s2 := Dup(s1, 2);
      assert s2.stack[7] == 0xcc;
      var s3 := SLoad(s2);
      assert s3.stack[7] == 0xcc;
      var s4 := Dup(s3, 2);
      assert s4.stack[8] == 0xcc;
      var s5 := MStore(s4);
      assert s5.stack[6] == 0xcc;
      var s6 := Swap(s5, 1);
      assert s6.stack[6] == 0xcc;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[7] == 0xcc;
      var s8 := Add(s7);
      assert s8.stack[6] == 0xcc;
      var s9 := Swap(s8, 1);
      assert s9.stack[6] == 0xcc;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[7] == 0xcc;
      var s11 := Add(s10);
      assert s11.stack[6] == 0xcc;
      var s12 := Dup(s11, 1);
      assert s12.stack[7] == 0xcc;
      var s13 := Dup(s12, 4);
      assert s13.stack[8] == 0xcc;
      var s14 := Gt(s13);
      assert s14.stack[7] == 0xcc;
      var s15 := PushN(s14, 2, 0x0556);
      assert s15.stack[0] == 0x556;
      assert s15.stack[8] == 0xcc;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s16, gas - 1)
      else
        ExecuteFromCFGNode_s134(s16, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 77
    * Starting at 0x56a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x56a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xcc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[7] == 0xcc;
      var s2 := Swap(s1, 1);
      assert s2.stack[7] == 0xcc;
      var s3 := Sub(s2);
      assert s3.stack[6] == 0xcc;
      var s4 := PushN(s3, 1, 0x1f);
      assert s4.stack[7] == 0xcc;
      var s5 := And(s4);
      assert s5.stack[6] == 0xcc;
      var s6 := Dup(s5, 3);
      assert s6.stack[7] == 0xcc;
      var s7 := Add(s6);
      assert s7.stack[6] == 0xcc;
      var s8 := Swap(s7, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s124(s8, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 12
    * Starting at 0xaf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x00b7);
      assert s2.stack[0] == 0xb7;
      var s3 := PushN(s2, 2, 0x0440);
      assert s3.stack[0] == 0x440;
      assert s3.stack[1] == 0xb7;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s4, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 69
    * Starting at 0x440
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x440 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0xb7;
      var s2 := CallValue(s1);
      assert s2.stack[1] == 0xb7;
      var s3 := PushN(s2, 1, 0x03);
      assert s3.stack[2] == 0xb7;
      var s4 := PushN(s3, 1, 0x00);
      assert s4.stack[3] == 0xb7;
      var s5 := Caller(s4);
      assert s5.stack[4] == 0xb7;
      var s6 := PushN(s5, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s6.stack[5] == 0xb7;
      var s7 := And(s6);
      assert s7.stack[4] == 0xb7;
      var s8 := PushN(s7, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s8.stack[5] == 0xb7;
      var s9 := And(s8);
      assert s9.stack[4] == 0xb7;
      var s10 := Dup(s9, 2);
      assert s10.stack[5] == 0xb7;
      var s11 := MStore(s10);
      assert s11.stack[3] == 0xb7;
      var s12 := PushN(s11, 1, 0x20);
      assert s12.stack[4] == 0xb7;
      var s13 := Add(s12);
      assert s13.stack[3] == 0xb7;
      var s14 := Swap(s13, 1);
      assert s14.stack[3] == 0xb7;
      var s15 := Dup(s14, 2);
      assert s15.stack[4] == 0xb7;
      var s16 := MStore(s15);
      assert s16.stack[2] == 0xb7;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[3] == 0xb7;
      var s18 := Add(s17);
      assert s18.stack[2] == 0xb7;
      var s19 := PushN(s18, 1, 0x00);
      assert s19.stack[3] == 0xb7;
      var s20 := Keccak256(s19);
      assert s20.stack[2] == 0xb7;
      var s21 := PushN(s20, 1, 0x00);
      assert s21.stack[3] == 0xb7;
      var s22 := Dup(s21, 3);
      assert s22.stack[4] == 0xb7;
      var s23 := Dup(s22, 3);
      assert s23.stack[5] == 0xb7;
      var s24 := SLoad(s23);
      assert s24.stack[5] == 0xb7;
      var s25 := Add(s24);
      assert s25.stack[4] == 0xb7;
      var s26 := Swap(s25, 3);
      assert s26.stack[4] == 0xb7;
      var s27 := Pop(s26);
      assert s27.stack[3] == 0xb7;
      var s28 := Pop(s27);
      assert s28.stack[2] == 0xb7;
      var s29 := Dup(s28, 2);
      assert s29.stack[3] == 0xb7;
      var s30 := Swap(s29, 1);
      assert s30.stack[3] == 0xb7;
      var s31 := SStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s137(s31, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 70
    * Starting at 0x48d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[1] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.stack[0] == 0xb7;
      var s2 := Caller(s1);
      assert s2.stack[1] == 0xb7;
      var s3 := PushN(s2, 20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s3.stack[2] == 0xb7;
      var s4 := And(s3);
      assert s4.stack[1] == 0xb7;
      var s5 := PushN(s4, 32, 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c);
      assert s5.stack[2] == 0xb7;
      var s6 := CallValue(s5);
      assert s6.stack[3] == 0xb7;
      var s7 := PushN(s6, 1, 0x40);
      assert s7.stack[4] == 0xb7;
      var s8 := MLoad(s7);
      assert s8.stack[4] == 0xb7;
      var s9 := Dup(s8, 1);
      assert s9.stack[5] == 0xb7;
      var s10 := Dup(s9, 3);
      assert s10.stack[6] == 0xb7;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0xb7;
      var s12 := MStore(s11);
      assert s12.stack[5] == 0xb7;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[6] == 0xb7;
      var s14 := Add(s13);
      assert s14.stack[5] == 0xb7;
      var s15 := Swap(s14, 2);
      assert s15.stack[5] == 0xb7;
      var s16 := Pop(s15);
      assert s16.stack[4] == 0xb7;
      var s17 := Pop(s16);
      assert s17.stack[3] == 0xb7;
      var s18 := PushN(s17, 1, 0x40);
      assert s18.stack[4] == 0xb7;
      var s19 := MLoad(s18);
      assert s19.stack[4] == 0xb7;
      var s20 := Dup(s19, 1);
      assert s20.stack[5] == 0xb7;
      var s21 := Swap(s20, 2);
      assert s21.stack[5] == 0xb7;
      var s22 := Sub(s21);
      assert s22.stack[4] == 0xb7;
      var s23 := Swap(s22, 1);
      assert s23.stack[4] == 0xb7;
      var s24 := LogN(s23, 2);
      assert s24.stack[0] == 0xb7;
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s25, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 13
    * Starting at 0xb7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Stop(s1);
      // Segment is terminal (Revert, Stop or Return)
      s2
  }
}
