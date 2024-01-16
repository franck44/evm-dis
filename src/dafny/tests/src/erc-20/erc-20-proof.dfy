
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
      var s7 := PushN(s6, 2, 0x00b9);
      assert s7.stack[0] == 0xb9;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s8, gas - 1)
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
      var s1 := PushN(s0, 4, 0xffffffff);
      var s2 := PushN(s1, 29, 0x0100000000000000000000000000000000000000000000000000000000);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := CallDataLoad(s3);
      var s5 := Div(s4);
      var s6 := And(s5);
      var s7 := PushN(s6, 4, 0x06fdde03);
      var s8 := Dup(s7, 2);
      var s9 := Eq(s8);
      var s10 := PushN(s9, 2, 0x00be);
      assert s10.stack[0] == 0xbe;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s134(s11, gas - 1)
      else
        ExecuteFromCFGNode_s2(s11, gas - 1)
  }
 
  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x40
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */ 
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x0148);
      assert s4.stack[0] == 0x148;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s129(s5, gas - 1)
      else
        ExecuteFromCFGNode_s3(s5, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x4b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x017e);
      assert s4.stack[0] == 0x17e;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s125(s5, gas - 1)
      else
        ExecuteFromCFGNode_s4(s5, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x56
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x01a3);
      assert s4.stack[0] == 0x1a3;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s104(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x61
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x01cb);
      assert s4.stack[0] == 0x1cb;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s99(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x6c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x42966c68);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x01f4);
      assert s4.stack[0] == 0x1f4;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x77
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x020a);
      assert s4.stack[0] == 0x20a;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x82
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x79cc6790);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x0229);
      assert s4.stack[0] == 0x229;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x8d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x024b);
      assert s4.stack[0] == 0x24b;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 10
    * Starting at 0x98
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x025e);
      assert s4.stack[0] == 0x25e;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s5, gas - 1)
      else
        ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 11
    * Starting at 0xa3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0xcae9ca51);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x0282);
      assert s4.stack[0] == 0x282;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s5, gas - 1)
      else
        ExecuteFromCFGNode_s12(s5, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 12
    * Starting at 0xae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      var s2 := PushN(s1, 4, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := PushN(s3, 2, 0x02e7);
      assert s4.stack[0] == 0x2e7;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s5, gas - 1)
      else
        ExecuteFromCFGNode_s13(s5, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 13
    * Starting at 0xb9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
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

  /** Node 14
    * Segment Id for this node is: 59
    * Starting at 0x2e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x02f2);
      assert s4.stack[0] == 0x2f2;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s5, gas - 1)
      else
        ExecuteFromCFGNode_s15(s5, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 60
    * Starting at 0x2ee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ee as nat
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

  /** Node 16
    * Segment Id for this node is: 61
    * Starting at 0x2f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0191);
      assert s2.stack[0] == 0x191;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[1] == 0x191;
      var s4 := PushN(s3, 1, 0xa0);
      assert s4.stack[2] == 0x191;
      var s5 := PushN(s4, 1, 0x02);
      assert s5.stack[3] == 0x191;
      var s6 := Exp(s5);
      assert s6.stack[2] == 0x191;
      var s7 := Sub(s6);
      assert s7.stack[1] == 0x191;
      var s8 := PushN(s7, 1, 0x04);
      assert s8.stack[2] == 0x191;
      var s9 := CallDataLoad(s8);
      assert s9.stack[2] == 0x191;
      var s10 := Dup(s9, 2);
      assert s10.stack[3] == 0x191;
      var s11 := And(s10);
      assert s11.stack[2] == 0x191;
      var s12 := Swap(s11, 1);
      assert s12.stack[2] == 0x191;
      var s13 := PushN(s12, 1, 0x24);
      assert s13.stack[3] == 0x191;
      var s14 := CallDataLoad(s13);
      assert s14.stack[3] == 0x191;
      var s15 := And(s14);
      assert s15.stack[2] == 0x191;
      var s16 := PushN(s15, 2, 0x0785);
      assert s16.stack[0] == 0x785;
      assert s16.stack[3] == 0x191;
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s17, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 114
    * Starting at 0x785
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x785 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x191

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x191;
      var s2 := PushN(s1, 1, 0x05);
      assert s2.stack[3] == 0x191;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[4] == 0x191;
      var s4 := Swap(s3, 1);
      assert s4.stack[4] == 0x191;
      var s5 := Dup(s4, 2);
      assert s5.stack[5] == 0x191;
      var s6 := MStore(s5);
      assert s6.stack[3] == 0x191;
      var s7 := PushN(s6, 1, 0x00);
      assert s7.stack[4] == 0x191;
      var s8 := Swap(s7, 3);
      assert s8.stack[4] == 0x191;
      var s9 := Dup(s8, 4);
      assert s9.stack[5] == 0x191;
      var s10 := MStore(s9);
      assert s10.stack[3] == 0x191;
      var s11 := PushN(s10, 1, 0x40);
      assert s11.stack[4] == 0x191;
      var s12 := Dup(s11, 1);
      assert s12.stack[5] == 0x191;
      var s13 := Dup(s12, 5);
      assert s13.stack[6] == 0x191;
      var s14 := Keccak256(s13);
      assert s14.stack[5] == 0x191;
      var s15 := Swap(s14, 1);
      assert s15.stack[5] == 0x191;
      var s16 := Swap(s15, 2);
      assert s16.stack[5] == 0x191;
      var s17 := MStore(s16);
      assert s17.stack[3] == 0x191;
      var s18 := Swap(s17, 1);
      assert s18.stack[3] == 0x191;
      var s19 := Dup(s18, 3);
      assert s19.stack[4] == 0x191;
      var s20 := MStore(s19);
      assert s20.stack[2] == 0x191;
      var s21 := Swap(s20, 1);
      assert s21.stack[2] == 0x191;
      var s22 := Keccak256(s21);
      assert s22.stack[1] == 0x191;
      var s23 := SLoad(s22);
      assert s23.stack[1] == 0x191;
      var s24 := Dup(s23, 2);
      assert s24.stack[0] == 0x191;
      assert s24.stack[2] == 0x191;
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s25, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 30
    * Starting at 0x191
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x191

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x191;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0x191;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x191;
      var s4 := Swap(s3, 1);
      assert s4.stack[2] == 0x191;
      var s5 := Dup(s4, 2);
      assert s5.stack[3] == 0x191;
      var s6 := MStore(s5);
      assert s6.stack[1] == 0x191;
      var s7 := PushN(s6, 1, 0x20);
      assert s7.stack[2] == 0x191;
      var s8 := Add(s7);
      assert s8.stack[1] == 0x191;
      var s9 := PushN(s8, 1, 0x40);
      assert s9.stack[2] == 0x191;
      var s10 := MLoad(s9);
      assert s10.stack[2] == 0x191;
      var s11 := Dup(s10, 1);
      assert s11.stack[3] == 0x191;
      var s12 := Swap(s11, 2);
      assert s12.stack[3] == 0x191;
      var s13 := Sub(s12);
      assert s13.stack[2] == 0x191;
      var s14 := Swap(s13, 1);
      assert s14.stack[2] == 0x191;
      var s15 := Return(s14);
      // Segment is terminal (Revert, Stop or Return)
      s15
  }

  /** Node 19
    * Segment Id for this node is: 54
    * Starting at 0x282
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x282 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x028d);
      assert s4.stack[0] == 0x28d;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s5, gas - 1)
      else
        ExecuteFromCFGNode_s20(s5, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 55
    * Starting at 0x289
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x289 as nat
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

  /** Node 21
    * Segment Id for this node is: 56
    * Starting at 0x28d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x016a);
      assert s2.stack[0] == 0x16a;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[1] == 0x16a;
      var s4 := Dup(s3, 1);
      assert s4.stack[2] == 0x16a;
      var s5 := CallDataLoad(s4);
      assert s5.stack[2] == 0x16a;
      var s6 := PushN(s5, 1, 0x01);
      assert s6.stack[3] == 0x16a;
      var s7 := PushN(s6, 1, 0xa0);
      assert s7.stack[4] == 0x16a;
      var s8 := PushN(s7, 1, 0x02);
      assert s8.stack[5] == 0x16a;
      var s9 := Exp(s8);
      assert s9.stack[4] == 0x16a;
      var s10 := Sub(s9);
      assert s10.stack[3] == 0x16a;
      var s11 := And(s10);
      assert s11.stack[2] == 0x16a;
      var s12 := Swap(s11, 1);
      assert s12.stack[2] == 0x16a;
      var s13 := PushN(s12, 1, 0x24);
      assert s13.stack[3] == 0x16a;
      var s14 := Dup(s13, 1);
      assert s14.stack[4] == 0x16a;
      var s15 := CallDataLoad(s14);
      assert s15.stack[4] == 0x16a;
      var s16 := Swap(s15, 2);
      assert s16.stack[4] == 0x16a;
      var s17 := Swap(s16, 1);
      assert s17.stack[4] == 0x16a;
      var s18 := PushN(s17, 1, 0x64);
      assert s18.stack[5] == 0x16a;
      var s19 := Swap(s18, 1);
      assert s19.stack[5] == 0x16a;
      var s20 := PushN(s19, 1, 0x44);
      assert s20.stack[6] == 0x16a;
      var s21 := CallDataLoad(s20);
      assert s21.stack[6] == 0x16a;
      var s22 := Swap(s21, 1);
      assert s22.stack[6] == 0x16a;
      var s23 := Dup(s22, 2);
      assert s23.stack[7] == 0x16a;
      var s24 := Add(s23);
      assert s24.stack[6] == 0x16a;
      var s25 := Swap(s24, 1);
      assert s25.stack[6] == 0x16a;
      var s26 := Dup(s25, 4);
      assert s26.stack[7] == 0x16a;
      var s27 := Add(s26);
      assert s27.stack[6] == 0x16a;
      var s28 := CallDataLoad(s27);
      assert s28.stack[6] == 0x16a;
      var s29 := Dup(s28, 1);
      assert s29.stack[7] == 0x16a;
      var s30 := PushN(s29, 1, 0x20);
      assert s30.stack[8] == 0x16a;
      var s31 := PushN(s30, 1, 0x1f);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s22(s31, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 57
    * Starting at 0x2b7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[10] == 0x16a;
      var s2 := Add(s1);
      assert s2.stack[9] == 0x16a;
      var s3 := Dup(s2, 2);
      assert s3.stack[10] == 0x16a;
      var s4 := Swap(s3, 1);
      assert s4.stack[10] == 0x16a;
      var s5 := Div(s4);
      assert s5.stack[9] == 0x16a;
      var s6 := Dup(s5, 2);
      assert s6.stack[10] == 0x16a;
      var s7 := Mul(s6);
      assert s7.stack[9] == 0x16a;
      var s8 := Add(s7);
      assert s8.stack[8] == 0x16a;
      var s9 := PushN(s8, 1, 0x40);
      assert s9.stack[9] == 0x16a;
      var s10 := MLoad(s9);
      assert s10.stack[9] == 0x16a;
      var s11 := Swap(s10, 1);
      assert s11.stack[9] == 0x16a;
      var s12 := Dup(s11, 2);
      assert s12.stack[10] == 0x16a;
      var s13 := Add(s12);
      assert s13.stack[9] == 0x16a;
      var s14 := PushN(s13, 1, 0x40);
      assert s14.stack[10] == 0x16a;
      var s15 := MStore(s14);
      assert s15.stack[8] == 0x16a;
      var s16 := Dup(s15, 2);
      assert s16.stack[9] == 0x16a;
      var s17 := Dup(s16, 2);
      assert s17.stack[10] == 0x16a;
      var s18 := MStore(s17);
      assert s18.stack[8] == 0x16a;
      var s19 := Swap(s18, 3);
      assert s19.stack[8] == 0x16a;
      var s20 := Swap(s19, 2);
      assert s20.stack[8] == 0x16a;
      var s21 := Swap(s20, 1);
      assert s21.stack[8] == 0x16a;
      var s22 := PushN(s21, 1, 0x20);
      assert s22.stack[9] == 0x16a;
      var s23 := Dup(s22, 5);
      assert s23.stack[10] == 0x16a;
      var s24 := Add(s23);
      assert s24.stack[9] == 0x16a;
      var s25 := Dup(s24, 4);
      assert s25.stack[10] == 0x16a;
      var s26 := Dup(s25, 4);
      assert s26.stack[11] == 0x16a;
      var s27 := Dup(s26, 1);
      assert s27.stack[12] == 0x16a;
      var s28 := Dup(s27, 3);
      assert s28.stack[13] == 0x16a;
      var s29 := Dup(s28, 5);
      assert s29.stack[14] == 0x16a;
      var s30 := CallDataCopy(s29);
      assert s30.stack[11] == 0x16a;
      var s31 := Pop(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s23(s31, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 58
    * Starting at 0x2d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 5);
      assert s1.stack[10] == 0x16a;
      var s2 := Swap(s1, 7);
      assert s2.stack[10] == 0x16a;
      var s3 := Pop(s2);
      assert s3.stack[9] == 0x16a;
      var s4 := PushN(s3, 2, 0x0653);
      assert s4.stack[0] == 0x653;
      assert s4.stack[10] == 0x16a;
      var s5 := Swap(s4, 6);
      assert s5.stack[6] == 0x653;
      assert s5.stack[10] == 0x16a;
      var s6 := Pop(s5);
      assert s6.stack[5] == 0x653;
      assert s6.stack[9] == 0x16a;
      var s7 := Pop(s6);
      assert s7.stack[4] == 0x653;
      assert s7.stack[8] == 0x16a;
      var s8 := Pop(s7);
      assert s8.stack[3] == 0x653;
      assert s8.stack[7] == 0x16a;
      var s9 := Pop(s8);
      assert s9.stack[2] == 0x653;
      assert s9.stack[6] == 0x16a;
      var s10 := Pop(s9);
      assert s10.stack[1] == 0x653;
      assert s10.stack[5] == 0x16a;
      var s11 := Pop(s10);
      assert s11.stack[0] == 0x653;
      assert s11.stack[4] == 0x16a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s12, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 99
    * Starting at 0x653
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x653 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x16a;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[4] == 0x16a;
      var s3 := Dup(s2, 4);
      assert s3.stack[5] == 0x16a;
      var s4 := PushN(s3, 2, 0x0660);
      assert s4.stack[0] == 0x660;
      assert s4.stack[6] == 0x16a;
      var s5 := Dup(s4, 2);
      assert s5.stack[1] == 0x660;
      assert s5.stack[7] == 0x16a;
      var s6 := Dup(s5, 6);
      assert s6.stack[2] == 0x660;
      assert s6.stack[8] == 0x16a;
      var s7 := PushN(s6, 2, 0x03aa);
      assert s7.stack[0] == 0x3aa;
      assert s7.stack[3] == 0x660;
      assert s7.stack[9] == 0x16a;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s8, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 70
    * Starting at 0x3aa
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x660

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x660;
      assert s1.stack[8] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[3] == 0x660;
      assert s2.stack[9] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[4] == 0x660;
      assert s3.stack[10] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[5] == 0x660;
      assert s4.stack[11] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[4] == 0x660;
      assert s5.stack[10] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[3] == 0x660;
      assert s6.stack[9] == 0x16a;
      var s7 := Caller(s6);
      assert s7.stack[4] == 0x660;
      assert s7.stack[10] == 0x16a;
      var s8 := Dup(s7, 2);
      assert s8.stack[5] == 0x660;
      assert s8.stack[11] == 0x16a;
      var s9 := And(s8);
      assert s9.stack[4] == 0x660;
      assert s9.stack[10] == 0x16a;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[5] == 0x660;
      assert s10.stack[11] == 0x16a;
      var s11 := Swap(s10, 1);
      assert s11.stack[5] == 0x660;
      assert s11.stack[11] == 0x16a;
      var s12 := Dup(s11, 2);
      assert s12.stack[6] == 0x660;
      assert s12.stack[12] == 0x16a;
      var s13 := MStore(s12);
      assert s13.stack[4] == 0x660;
      assert s13.stack[10] == 0x16a;
      var s14 := PushN(s13, 1, 0x05);
      assert s14.stack[5] == 0x660;
      assert s14.stack[11] == 0x16a;
      var s15 := PushN(s14, 1, 0x20);
      assert s15.stack[6] == 0x660;
      assert s15.stack[12] == 0x16a;
      var s16 := Swap(s15, 1);
      assert s16.stack[6] == 0x660;
      assert s16.stack[12] == 0x16a;
      var s17 := Dup(s16, 2);
      assert s17.stack[7] == 0x660;
      assert s17.stack[13] == 0x16a;
      var s18 := MStore(s17);
      assert s18.stack[5] == 0x660;
      assert s18.stack[11] == 0x16a;
      var s19 := PushN(s18, 1, 0x40);
      assert s19.stack[6] == 0x660;
      assert s19.stack[12] == 0x16a;
      var s20 := Dup(s19, 1);
      assert s20.stack[7] == 0x660;
      assert s20.stack[13] == 0x16a;
      var s21 := Dup(s20, 4);
      assert s21.stack[8] == 0x660;
      assert s21.stack[14] == 0x16a;
      var s22 := Keccak256(s21);
      assert s22.stack[7] == 0x660;
      assert s22.stack[13] == 0x16a;
      var s23 := Swap(s22, 4);
      assert s23.stack[7] == 0x660;
      assert s23.stack[13] == 0x16a;
      var s24 := Dup(s23, 7);
      assert s24.stack[8] == 0x660;
      assert s24.stack[14] == 0x16a;
      var s25 := And(s24);
      assert s25.stack[7] == 0x660;
      assert s25.stack[13] == 0x16a;
      var s26 := Dup(s25, 4);
      assert s26.stack[8] == 0x660;
      assert s26.stack[14] == 0x16a;
      var s27 := MStore(s26);
      assert s27.stack[6] == 0x660;
      assert s27.stack[12] == 0x16a;
      var s28 := Swap(s27, 3);
      assert s28.stack[6] == 0x660;
      assert s28.stack[12] == 0x16a;
      var s29 := Swap(s28, 1);
      assert s29.stack[6] == 0x660;
      assert s29.stack[12] == 0x16a;
      var s30 := MStore(s29);
      assert s30.stack[4] == 0x660;
      assert s30.stack[10] == 0x16a;
      var s31 := Keccak256(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s26(s31, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 71
    * Starting at 0x3d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x660

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[4] == 0x660;
      assert s1.stack[10] == 0x16a;
      var s2 := Swap(s1, 1);
      assert s2.stack[4] == 0x660;
      assert s2.stack[10] == 0x16a;
      var s3 := SStore(s2);
      assert s3.stack[2] == 0x660;
      assert s3.stack[8] == 0x16a;
      var s4 := PushN(s3, 1, 0x01);
      assert s4.stack[3] == 0x660;
      assert s4.stack[9] == 0x16a;
      var s5 := Swap(s4, 3);
      assert s5.stack[0] == 0x660;
      assert s5.stack[9] == 0x16a;
      var s6 := Swap(s5, 2);
      assert s6.stack[2] == 0x660;
      assert s6.stack[9] == 0x16a;
      var s7 := Pop(s6);
      assert s7.stack[1] == 0x660;
      assert s7.stack[8] == 0x16a;
      var s8 := Pop(s7);
      assert s8.stack[0] == 0x660;
      assert s8.stack[7] == 0x16a;
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s9, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 100
    * Starting at 0x660
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x660 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0x16a;
      var s2 := IsZero(s1);
      assert s2.stack[6] == 0x16a;
      var s3 := PushN(s2, 2, 0x077d);
      assert s3.stack[0] == 0x77d;
      assert s3.stack[7] == 0x16a;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s40(s4, gas - 1)
      else
        ExecuteFromCFGNode_s28(s4, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 101
    * Starting at 0x666
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x666 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[6] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[7] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[8] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[9] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[8] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[7] == 0x16a;
      var s7 := And(s6);
      assert s7.stack[6] == 0x16a;
      var s8 := PushN(s7, 4, 0x8f4ffcb1);
      assert s8.stack[7] == 0x16a;
      var s9 := Caller(s8);
      assert s9.stack[8] == 0x16a;
      var s10 := Dup(s9, 7);
      assert s10.stack[9] == 0x16a;
      var s11 := Address(s10);
      assert s11.stack[10] == 0x16a;
      var s12 := Dup(s11, 8);
      assert s12.stack[11] == 0x16a;
      var s13 := PushN(s12, 1, 0x40);
      assert s13.stack[12] == 0x16a;
      var s14 := MLoad(s13);
      assert s14.stack[12] == 0x16a;
      var s15 := Dup(s14, 6);
      assert s15.stack[13] == 0x16a;
      var s16 := PushN(s15, 4, 0xffffffff);
      assert s16.stack[14] == 0x16a;
      var s17 := And(s16);
      assert s17.stack[13] == 0x16a;
      var s18 := PushN(s17, 29, 0x0100000000000000000000000000000000000000000000000000000000);
      assert s18.stack[14] == 0x16a;
      var s19 := Mul(s18);
      assert s19.stack[13] == 0x16a;
      var s20 := Dup(s19, 2);
      assert s20.stack[14] == 0x16a;
      var s21 := MStore(s20);
      assert s21.stack[12] == 0x16a;
      var s22 := PushN(s21, 1, 0x04);
      assert s22.stack[13] == 0x16a;
      var s23 := Add(s22);
      assert s23.stack[12] == 0x16a;
      var s24 := Dup(s23, 1);
      assert s24.stack[13] == 0x16a;
      var s25 := Dup(s24, 6);
      assert s25.stack[14] == 0x16a;
      var s26 := PushN(s25, 1, 0x01);
      assert s26.stack[15] == 0x16a;
      var s27 := PushN(s26, 1, 0xa0);
      assert s27.stack[16] == 0x16a;
      var s28 := PushN(s27, 1, 0x02);
      assert s28.stack[17] == 0x16a;
      var s29 := Exp(s28);
      assert s29.stack[16] == 0x16a;
      var s30 := Sub(s29);
      assert s30.stack[15] == 0x16a;
      var s31 := And(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s29(s31, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 102
    * Starting at 0x6b2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x01);
      assert s1.stack[15] == 0x16a;
      var s2 := PushN(s1, 1, 0xa0);
      assert s2.stack[16] == 0x16a;
      var s3 := PushN(s2, 1, 0x02);
      assert s3.stack[17] == 0x16a;
      var s4 := Exp(s3);
      assert s4.stack[16] == 0x16a;
      var s5 := Sub(s4);
      assert s5.stack[15] == 0x16a;
      var s6 := And(s5);
      assert s6.stack[14] == 0x16a;
      var s7 := Dup(s6, 2);
      assert s7.stack[15] == 0x16a;
      var s8 := MStore(s7);
      assert s8.stack[13] == 0x16a;
      var s9 := PushN(s8, 1, 0x20);
      assert s9.stack[14] == 0x16a;
      var s10 := Add(s9);
      assert s10.stack[13] == 0x16a;
      var s11 := Dup(s10, 5);
      assert s11.stack[14] == 0x16a;
      var s12 := Dup(s11, 2);
      assert s12.stack[15] == 0x16a;
      var s13 := MStore(s12);
      assert s13.stack[13] == 0x16a;
      var s14 := PushN(s13, 1, 0x20);
      assert s14.stack[14] == 0x16a;
      var s15 := Add(s14);
      assert s15.stack[13] == 0x16a;
      var s16 := Dup(s15, 4);
      assert s16.stack[14] == 0x16a;
      var s17 := PushN(s16, 1, 0x01);
      assert s17.stack[15] == 0x16a;
      var s18 := PushN(s17, 1, 0xa0);
      assert s18.stack[16] == 0x16a;
      var s19 := PushN(s18, 1, 0x02);
      assert s19.stack[17] == 0x16a;
      var s20 := Exp(s19);
      assert s20.stack[16] == 0x16a;
      var s21 := Sub(s20);
      assert s21.stack[15] == 0x16a;
      var s22 := And(s21);
      assert s22.stack[14] == 0x16a;
      var s23 := PushN(s22, 1, 0x01);
      assert s23.stack[15] == 0x16a;
      var s24 := PushN(s23, 1, 0xa0);
      assert s24.stack[16] == 0x16a;
      var s25 := PushN(s24, 1, 0x02);
      assert s25.stack[17] == 0x16a;
      var s26 := Exp(s25);
      assert s26.stack[16] == 0x16a;
      var s27 := Sub(s26);
      assert s27.stack[15] == 0x16a;
      var s28 := And(s27);
      assert s28.stack[14] == 0x16a;
      var s29 := Dup(s28, 2);
      assert s29.stack[15] == 0x16a;
      var s30 := MStore(s29);
      assert s30.stack[13] == 0x16a;
      var s31 := PushN(s30, 1, 0x20);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s30(s31, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 103
    * Starting at 0x6dd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      assert s1.stack[13] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[14] == 0x16a;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[15] == 0x16a;
      var s4 := Add(s3);
      assert s4.stack[14] == 0x16a;
      var s5 := Dup(s4, 3);
      assert s5.stack[15] == 0x16a;
      var s6 := Dup(s5, 2);
      assert s6.stack[16] == 0x16a;
      var s7 := Sub(s6);
      assert s7.stack[15] == 0x16a;
      var s8 := Dup(s7, 3);
      assert s8.stack[16] == 0x16a;
      var s9 := MStore(s8);
      assert s9.stack[14] == 0x16a;
      var s10 := Dup(s9, 4);
      assert s10.stack[15] == 0x16a;
      var s11 := Dup(s10, 2);
      assert s11.stack[16] == 0x16a;
      var s12 := Dup(s11, 2);
      assert s12.stack[17] == 0x16a;
      var s13 := MLoad(s12);
      assert s13.stack[17] == 0x16a;
      var s14 := Dup(s13, 2);
      assert s14.stack[18] == 0x16a;
      var s15 := MStore(s14);
      assert s15.stack[16] == 0x16a;
      var s16 := PushN(s15, 1, 0x20);
      assert s16.stack[17] == 0x16a;
      var s17 := Add(s16);
      assert s17.stack[16] == 0x16a;
      var s18 := Swap(s17, 2);
      assert s18.stack[16] == 0x16a;
      var s19 := Pop(s18);
      assert s19.stack[15] == 0x16a;
      var s20 := Dup(s19, 1);
      assert s20.stack[16] == 0x16a;
      var s21 := MLoad(s20);
      assert s21.stack[16] == 0x16a;
      var s22 := Swap(s21, 1);
      assert s22.stack[16] == 0x16a;
      var s23 := PushN(s22, 1, 0x20);
      assert s23.stack[17] == 0x16a;
      var s24 := Add(s23);
      assert s24.stack[16] == 0x16a;
      var s25 := Swap(s24, 1);
      assert s25.stack[16] == 0x16a;
      var s26 := Dup(s25, 1);
      assert s26.stack[17] == 0x16a;
      var s27 := Dup(s26, 4);
      assert s27.stack[18] == 0x16a;
      var s28 := Dup(s27, 4);
      assert s28.stack[19] == 0x16a;
      var s29 := PushN(s28, 1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s31(s29, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 104
    * Starting at 0x6fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[20] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[20] == 0x16a;
      var s2 := Dup(s1, 4);
      assert s2.stack[21] == 0x16a;
      var s3 := Dup(s2, 2);
      assert s3.stack[22] == 0x16a;
      var s4 := Lt(s3);
      assert s4.stack[21] == 0x16a;
      var s5 := IsZero(s4);
      assert s5.stack[21] == 0x16a;
      var s6 := PushN(s5, 2, 0x0716);
      assert s6.stack[0] == 0x716;
      assert s6.stack[22] == 0x16a;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s7, gas - 1)
      else
        ExecuteFromCFGNode_s32(s7, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 105
    * Starting at 0x707
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x707 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[20] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[21] == 0x16a;
      var s2 := Dup(s1, 3);
      assert s2.stack[22] == 0x16a;
      var s3 := Add(s2);
      assert s3.stack[21] == 0x16a;
      var s4 := MLoad(s3);
      assert s4.stack[21] == 0x16a;
      var s5 := Dup(s4, 4);
      assert s5.stack[22] == 0x16a;
      var s6 := Dup(s5, 3);
      assert s6.stack[23] == 0x16a;
      var s7 := Add(s6);
      assert s7.stack[22] == 0x16a;
      var s8 := MStore(s7);
      assert s8.stack[20] == 0x16a;
      var s9 := PushN(s8, 1, 0x20);
      assert s9.stack[21] == 0x16a;
      var s10 := Add(s9);
      assert s10.stack[20] == 0x16a;
      var s11 := PushN(s10, 2, 0x06fe);
      assert s11.stack[0] == 0x6fe;
      assert s11.stack[21] == 0x16a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s12, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 106
    * Starting at 0x716
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x716 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[20] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[20] == 0x16a;
      var s2 := Pop(s1);
      assert s2.stack[19] == 0x16a;
      var s3 := Pop(s2);
      assert s3.stack[18] == 0x16a;
      var s4 := Pop(s3);
      assert s4.stack[17] == 0x16a;
      var s5 := Pop(s4);
      assert s5.stack[16] == 0x16a;
      var s6 := Swap(s5, 1);
      assert s6.stack[16] == 0x16a;
      var s7 := Pop(s6);
      assert s7.stack[15] == 0x16a;
      var s8 := Swap(s7, 1);
      assert s8.stack[15] == 0x16a;
      var s9 := Dup(s8, 2);
      assert s9.stack[16] == 0x16a;
      var s10 := Add(s9);
      assert s10.stack[15] == 0x16a;
      var s11 := Swap(s10, 1);
      assert s11.stack[15] == 0x16a;
      var s12 := PushN(s11, 1, 0x1f);
      assert s12.stack[16] == 0x16a;
      var s13 := And(s12);
      assert s13.stack[15] == 0x16a;
      var s14 := Dup(s13, 1);
      assert s14.stack[16] == 0x16a;
      var s15 := IsZero(s14);
      assert s15.stack[16] == 0x16a;
      var s16 := PushN(s15, 2, 0x0743);
      assert s16.stack[0] == 0x743;
      assert s16.stack[17] == 0x16a;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s17, gas - 1)
      else
        ExecuteFromCFGNode_s34(s17, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 107
    * Starting at 0x72a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[16] == 0x16a;
      var s2 := Dup(s1, 3);
      assert s2.stack[17] == 0x16a;
      var s3 := Sub(s2);
      assert s3.stack[16] == 0x16a;
      var s4 := Dup(s3, 1);
      assert s4.stack[17] == 0x16a;
      var s5 := MLoad(s4);
      assert s5.stack[17] == 0x16a;
      var s6 := PushN(s5, 1, 0x01);
      assert s6.stack[18] == 0x16a;
      var s7 := Dup(s6, 4);
      assert s7.stack[19] == 0x16a;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[20] == 0x16a;
      var s9 := Sub(s8);
      assert s9.stack[19] == 0x16a;
      var s10 := PushN(s9, 2, 0x0100);
      assert s10.stack[20] == 0x16a;
      var s11 := Exp(s10);
      assert s11.stack[19] == 0x16a;
      var s12 := Sub(s11);
      assert s12.stack[18] == 0x16a;
      var s13 := Not(s12);
      assert s13.stack[18] == 0x16a;
      var s14 := And(s13);
      assert s14.stack[17] == 0x16a;
      var s15 := Dup(s14, 2);
      assert s15.stack[18] == 0x16a;
      var s16 := MStore(s15);
      assert s16.stack[16] == 0x16a;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[17] == 0x16a;
      var s18 := Add(s17);
      assert s18.stack[16] == 0x16a;
      var s19 := Swap(s18, 2);
      assert s19.stack[16] == 0x16a;
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s35(s20, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 108
    * Starting at 0x743
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x743 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[15] == 0x16a;
      var s2 := Pop(s1);
      assert s2.stack[14] == 0x16a;
      var s3 := Swap(s2, 6);
      assert s3.stack[14] == 0x16a;
      var s4 := Pop(s3);
      assert s4.stack[13] == 0x16a;
      var s5 := Pop(s4);
      assert s5.stack[12] == 0x16a;
      var s6 := Pop(s5);
      assert s6.stack[11] == 0x16a;
      var s7 := Pop(s6);
      assert s7.stack[10] == 0x16a;
      var s8 := Pop(s7);
      assert s8.stack[9] == 0x16a;
      var s9 := Pop(s8);
      assert s9.stack[8] == 0x16a;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[9] == 0x16a;
      var s11 := PushN(s10, 1, 0x40);
      assert s11.stack[10] == 0x16a;
      var s12 := MLoad(s11);
      assert s12.stack[10] == 0x16a;
      var s13 := Dup(s12, 1);
      assert s13.stack[11] == 0x16a;
      var s14 := Dup(s13, 4);
      assert s14.stack[12] == 0x16a;
      var s15 := Sub(s14);
      assert s15.stack[11] == 0x16a;
      var s16 := Dup(s15, 2);
      assert s16.stack[12] == 0x16a;
      var s17 := PushN(s16, 1, 0x00);
      assert s17.stack[13] == 0x16a;
      var s18 := Dup(s17, 8);
      assert s18.stack[14] == 0x16a;
      var s19 := Dup(s18, 1);
      assert s19.stack[15] == 0x16a;
      var s20 := ExtCodeSize(s19);
      assert s20.stack[15] == 0x16a;
      var s21 := IsZero(s20);
      assert s21.stack[15] == 0x16a;
      var s22 := IsZero(s21);
      assert s22.stack[15] == 0x16a;
      var s23 := PushN(s22, 2, 0x0764);
      assert s23.stack[0] == 0x764;
      assert s23.stack[16] == 0x16a;
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s24, gas - 1)
      else
        ExecuteFromCFGNode_s36(s24, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 109
    * Starting at 0x760
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x760 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[15] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[16] == 0x16a;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 37
    * Segment Id for this node is: 110
    * Starting at 0x764
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x764 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[14] == 0x16a;
      var s2 := PushN(s1, 2, 0x02c6);
      assert s2.stack[15] == 0x16a;
      var s3 := Gas(s2);
      assert s3.stack[16] == 0x16a;
      var s4 := Sub(s3);
      assert s4.stack[15] == 0x16a;
      var s5 := Call(s4);
      assert s5.stack[9] == 0x16a;
      var s6 := IsZero(s5);
      assert s6.stack[9] == 0x16a;
      var s7 := IsZero(s6);
      assert s7.stack[9] == 0x16a;
      var s8 := PushN(s7, 2, 0x0775);
      assert s8.stack[0] == 0x775;
      assert s8.stack[10] == 0x16a;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s9, gas - 1)
      else
        ExecuteFromCFGNode_s38(s9, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 111
    * Starting at 0x771
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x771 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[9] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[10] == 0x16a;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 39
    * Segment Id for this node is: 112
    * Starting at 0x775
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x775 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[8] == 0x16a;
      var s2 := Pop(s1);
      assert s2.stack[7] == 0x16a;
      var s3 := Pop(s2);
      assert s3.stack[6] == 0x16a;
      var s4 := Pop(s3);
      assert s4.stack[5] == 0x16a;
      var s5 := PushN(s4, 1, 0x01);
      assert s5.stack[6] == 0x16a;
      var s6 := Swap(s5, 2);
      assert s6.stack[6] == 0x16a;
      var s7 := Pop(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s40(s7, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 113
    * Starting at 0x77d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0x16a;
      var s2 := Pop(s1);
      assert s2.stack[4] == 0x16a;
      var s3 := Swap(s2, 4);
      assert s3.stack[0] == 0x16a;
      var s4 := Swap(s3, 3);
      assert s4.stack[3] == 0x16a;
      var s5 := Pop(s4);
      assert s5.stack[2] == 0x16a;
      var s6 := Pop(s5);
      assert s6.stack[1] == 0x16a;
      var s7 := Pop(s6);
      assert s7.stack[0] == 0x16a;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s8, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 26
    * Starting at 0x16a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap(s3, 1);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup(s6, 2);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x20);
      var s10 := Add(s9);
      var s11 := PushN(s10, 1, 0x40);
      var s12 := MLoad(s11);
      var s13 := Dup(s12, 1);
      var s14 := Swap(s13, 2);
      var s15 := Sub(s14);
      var s16 := Swap(s15, 1);
      var s17 := Return(s16);
      // Segment is terminal (Revert, Stop or Return)
      s17
  }

  /** Node 42
    * Segment Id for this node is: 50
    * Starting at 0x25e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x0269);
      assert s4.stack[0] == 0x269;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s44(s5, gas - 1)
      else
        ExecuteFromCFGNode_s43(s5, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 51
    * Starting at 0x265
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x265 as nat
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

  /** Node 44
    * Segment Id for this node is: 52
    * Starting at 0x269
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x269 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0280);
      assert s2.stack[0] == 0x280;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[1] == 0x280;
      var s4 := PushN(s3, 1, 0xa0);
      assert s4.stack[2] == 0x280;
      var s5 := PushN(s4, 1, 0x02);
      assert s5.stack[3] == 0x280;
      var s6 := Exp(s5);
      assert s6.stack[2] == 0x280;
      var s7 := Sub(s6);
      assert s7.stack[1] == 0x280;
      var s8 := PushN(s7, 1, 0x04);
      assert s8.stack[2] == 0x280;
      var s9 := CallDataLoad(s8);
      assert s9.stack[2] == 0x280;
      var s10 := And(s9);
      assert s10.stack[1] == 0x280;
      var s11 := PushN(s10, 1, 0x24);
      assert s11.stack[2] == 0x280;
      var s12 := CallDataLoad(s11);
      assert s12.stack[2] == 0x280;
      var s13 := PushN(s12, 2, 0x0644);
      assert s13.stack[0] == 0x644;
      assert s13.stack[3] == 0x280;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s14, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 97
    * Starting at 0x644
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x644 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x280;
      var s2 := PushN(s1, 2, 0x064f);
      assert s2.stack[0] == 0x64f;
      assert s2.stack[3] == 0x280;
      var s3 := Caller(s2);
      assert s3.stack[1] == 0x64f;
      assert s3.stack[4] == 0x280;
      var s4 := Dup(s3, 4);
      assert s4.stack[2] == 0x64f;
      assert s4.stack[5] == 0x280;
      var s5 := Dup(s4, 4);
      assert s5.stack[3] == 0x64f;
      assert s5.stack[6] == 0x280;
      var s6 := PushN(s5, 2, 0x07a2);
      assert s6.stack[0] == 0x7a2;
      assert s6.stack[4] == 0x64f;
      assert s6.stack[7] == 0x280;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s7, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 115
    * Starting at 0x7a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x64f

    requires s0.stack[6] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x64f;
      assert s1.stack[6] == 0x280;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[4] == 0x64f;
      assert s2.stack[7] == 0x280;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[5] == 0x64f;
      assert s3.stack[8] == 0x280;
      var s4 := PushN(s3, 1, 0xa0);
      assert s4.stack[6] == 0x64f;
      assert s4.stack[9] == 0x280;
      var s5 := PushN(s4, 1, 0x02);
      assert s5.stack[7] == 0x64f;
      assert s5.stack[10] == 0x280;
      var s6 := Exp(s5);
      assert s6.stack[6] == 0x64f;
      assert s6.stack[9] == 0x280;
      var s7 := Sub(s6);
      assert s7.stack[5] == 0x64f;
      assert s7.stack[8] == 0x280;
      var s8 := Dup(s7, 4);
      assert s8.stack[6] == 0x64f;
      assert s8.stack[9] == 0x280;
      var s9 := And(s8);
      assert s9.stack[5] == 0x64f;
      assert s9.stack[8] == 0x280;
      var s10 := IsZero(s9);
      assert s10.stack[5] == 0x64f;
      assert s10.stack[8] == 0x280;
      var s11 := IsZero(s10);
      assert s11.stack[5] == 0x64f;
      assert s11.stack[8] == 0x280;
      var s12 := PushN(s11, 2, 0x07b9);
      assert s12.stack[0] == 0x7b9;
      assert s12.stack[6] == 0x64f;
      assert s12.stack[9] == 0x280;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s13, gas - 1)
      else
        ExecuteFromCFGNode_s47(s13, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 116
    * Starting at 0x7b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x64f

    requires s0.stack[7] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x64f;
      assert s1.stack[8] == 0x280;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x64f;
      assert s2.stack[9] == 0x280;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 48
    * Segment Id for this node is: 117
    * Starting at 0x7b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x64f

    requires s0.stack[7] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x64f;
      assert s1.stack[7] == 0x280;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[5] == 0x64f;
      assert s2.stack[8] == 0x280;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[6] == 0x64f;
      assert s3.stack[9] == 0x280;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[7] == 0x64f;
      assert s4.stack[10] == 0x280;
      var s5 := Exp(s4);
      assert s5.stack[6] == 0x64f;
      assert s5.stack[9] == 0x280;
      var s6 := Sub(s5);
      assert s6.stack[5] == 0x64f;
      assert s6.stack[8] == 0x280;
      var s7 := Dup(s6, 5);
      assert s7.stack[6] == 0x64f;
      assert s7.stack[9] == 0x280;
      var s8 := And(s7);
      assert s8.stack[5] == 0x64f;
      assert s8.stack[8] == 0x280;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[6] == 0x64f;
      assert s9.stack[9] == 0x280;
      var s10 := Swap(s9, 1);
      assert s10.stack[6] == 0x64f;
      assert s10.stack[9] == 0x280;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x64f;
      assert s11.stack[10] == 0x280;
      var s12 := MStore(s11);
      assert s12.stack[5] == 0x64f;
      assert s12.stack[8] == 0x280;
      var s13 := PushN(s12, 1, 0x04);
      assert s13.stack[6] == 0x64f;
      assert s13.stack[9] == 0x280;
      var s14 := PushN(s13, 1, 0x20);
      assert s14.stack[7] == 0x64f;
      assert s14.stack[10] == 0x280;
      var s15 := MStore(s14);
      assert s15.stack[5] == 0x64f;
      assert s15.stack[8] == 0x280;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[6] == 0x64f;
      assert s16.stack[9] == 0x280;
      var s17 := Swap(s16, 1);
      assert s17.stack[6] == 0x64f;
      assert s17.stack[9] == 0x280;
      var s18 := Keccak256(s17);
      assert s18.stack[5] == 0x64f;
      assert s18.stack[8] == 0x280;
      var s19 := SLoad(s18);
      assert s19.stack[5] == 0x64f;
      assert s19.stack[8] == 0x280;
      var s20 := Dup(s19, 3);
      assert s20.stack[6] == 0x64f;
      assert s20.stack[9] == 0x280;
      var s21 := Swap(s20, 1);
      assert s21.stack[6] == 0x64f;
      assert s21.stack[9] == 0x280;
      var s22 := Lt(s21);
      assert s22.stack[5] == 0x64f;
      assert s22.stack[8] == 0x280;
      var s23 := IsZero(s22);
      assert s23.stack[5] == 0x64f;
      assert s23.stack[8] == 0x280;
      var s24 := PushN(s23, 2, 0x07df);
      assert s24.stack[0] == 0x7df;
      assert s24.stack[6] == 0x64f;
      assert s24.stack[9] == 0x280;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s25, gas - 1)
      else
        ExecuteFromCFGNode_s49(s25, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 118
    * Starting at 0x7db
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x64f

    requires s0.stack[7] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x64f;
      assert s1.stack[8] == 0x280;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x64f;
      assert s2.stack[9] == 0x280;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 50
    * Segment Id for this node is: 119
    * Starting at 0x7df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x64f

    requires s0.stack[7] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x64f;
      assert s1.stack[7] == 0x280;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[5] == 0x64f;
      assert s2.stack[8] == 0x280;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[6] == 0x64f;
      assert s3.stack[9] == 0x280;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[7] == 0x64f;
      assert s4.stack[10] == 0x280;
      var s5 := Exp(s4);
      assert s5.stack[6] == 0x64f;
      assert s5.stack[9] == 0x280;
      var s6 := Sub(s5);
      assert s6.stack[5] == 0x64f;
      assert s6.stack[8] == 0x280;
      var s7 := Dup(s6, 4);
      assert s7.stack[6] == 0x64f;
      assert s7.stack[9] == 0x280;
      var s8 := And(s7);
      assert s8.stack[5] == 0x64f;
      assert s8.stack[8] == 0x280;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[6] == 0x64f;
      assert s9.stack[9] == 0x280;
      var s10 := Swap(s9, 1);
      assert s10.stack[6] == 0x64f;
      assert s10.stack[9] == 0x280;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x64f;
      assert s11.stack[10] == 0x280;
      var s12 := MStore(s11);
      assert s12.stack[5] == 0x64f;
      assert s12.stack[8] == 0x280;
      var s13 := PushN(s12, 1, 0x04);
      assert s13.stack[6] == 0x64f;
      assert s13.stack[9] == 0x280;
      var s14 := PushN(s13, 1, 0x20);
      assert s14.stack[7] == 0x64f;
      assert s14.stack[10] == 0x280;
      var s15 := MStore(s14);
      assert s15.stack[5] == 0x64f;
      assert s15.stack[8] == 0x280;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[6] == 0x64f;
      assert s16.stack[9] == 0x280;
      var s17 := Swap(s16, 1);
      assert s17.stack[6] == 0x64f;
      assert s17.stack[9] == 0x280;
      var s18 := Keccak256(s17);
      assert s18.stack[5] == 0x64f;
      assert s18.stack[8] == 0x280;
      var s19 := SLoad(s18);
      assert s19.stack[5] == 0x64f;
      assert s19.stack[8] == 0x280;
      var s20 := Dup(s19, 3);
      assert s20.stack[6] == 0x64f;
      assert s20.stack[9] == 0x280;
      var s21 := Dup(s20, 2);
      assert s21.stack[7] == 0x64f;
      assert s21.stack[10] == 0x280;
      var s22 := Add(s21);
      assert s22.stack[6] == 0x64f;
      assert s22.stack[9] == 0x280;
      var s23 := Gt(s22);
      assert s23.stack[5] == 0x64f;
      assert s23.stack[8] == 0x280;
      var s24 := PushN(s23, 2, 0x0805);
      assert s24.stack[0] == 0x805;
      assert s24.stack[6] == 0x64f;
      assert s24.stack[9] == 0x280;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s25, gas - 1)
      else
        ExecuteFromCFGNode_s51(s25, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 120
    * Starting at 0x801
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x801 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x64f

    requires s0.stack[7] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x64f;
      assert s1.stack[8] == 0x280;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x64f;
      assert s2.stack[9] == 0x280;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 52
    * Segment Id for this node is: 121
    * Starting at 0x805
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x805 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x64f

    requires s0.stack[7] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x64f;
      assert s1.stack[7] == 0x280;
      var s2 := Pop(s1);
      assert s2.stack[3] == 0x64f;
      assert s2.stack[6] == 0x280;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[4] == 0x64f;
      assert s3.stack[7] == 0x280;
      var s4 := PushN(s3, 1, 0xa0);
      assert s4.stack[5] == 0x64f;
      assert s4.stack[8] == 0x280;
      var s5 := PushN(s4, 1, 0x02);
      assert s5.stack[6] == 0x64f;
      assert s5.stack[9] == 0x280;
      var s6 := Exp(s5);
      assert s6.stack[5] == 0x64f;
      assert s6.stack[8] == 0x280;
      var s7 := Sub(s6);
      assert s7.stack[4] == 0x64f;
      assert s7.stack[7] == 0x280;
      var s8 := Dup(s7, 1);
      assert s8.stack[5] == 0x64f;
      assert s8.stack[8] == 0x280;
      var s9 := Dup(s8, 4);
      assert s9.stack[6] == 0x64f;
      assert s9.stack[9] == 0x280;
      var s10 := And(s9);
      assert s10.stack[5] == 0x64f;
      assert s10.stack[8] == 0x280;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[6] == 0x64f;
      assert s11.stack[9] == 0x280;
      var s12 := Dup(s11, 2);
      assert s12.stack[7] == 0x64f;
      assert s12.stack[10] == 0x280;
      var s13 := Dup(s12, 2);
      assert s13.stack[8] == 0x64f;
      assert s13.stack[11] == 0x280;
      var s14 := MStore(s13);
      assert s14.stack[6] == 0x64f;
      assert s14.stack[9] == 0x280;
      var s15 := PushN(s14, 1, 0x04);
      assert s15.stack[7] == 0x64f;
      assert s15.stack[10] == 0x280;
      var s16 := PushN(s15, 1, 0x20);
      assert s16.stack[8] == 0x64f;
      assert s16.stack[11] == 0x280;
      var s17 := MStore(s16);
      assert s17.stack[6] == 0x64f;
      assert s17.stack[9] == 0x280;
      var s18 := PushN(s17, 1, 0x40);
      assert s18.stack[7] == 0x64f;
      assert s18.stack[10] == 0x280;
      var s19 := Dup(s18, 1);
      assert s19.stack[8] == 0x64f;
      assert s19.stack[11] == 0x280;
      var s20 := Dup(s19, 3);
      assert s20.stack[9] == 0x64f;
      assert s20.stack[12] == 0x280;
      var s21 := Keccak256(s20);
      assert s21.stack[8] == 0x64f;
      assert s21.stack[11] == 0x280;
      var s22 := Dup(s21, 1);
      assert s22.stack[9] == 0x64f;
      assert s22.stack[12] == 0x280;
      var s23 := SLoad(s22);
      assert s23.stack[9] == 0x64f;
      assert s23.stack[12] == 0x280;
      var s24 := Swap(s23, 5);
      assert s24.stack[9] == 0x64f;
      assert s24.stack[12] == 0x280;
      var s25 := Dup(s24, 9);
      assert s25.stack[10] == 0x64f;
      assert s25.stack[13] == 0x280;
      var s26 := And(s25);
      assert s26.stack[9] == 0x64f;
      assert s26.stack[12] == 0x280;
      var s27 := Dup(s26, 1);
      assert s27.stack[10] == 0x64f;
      assert s27.stack[13] == 0x280;
      var s28 := Dup(s27, 5);
      assert s28.stack[11] == 0x64f;
      assert s28.stack[14] == 0x280;
      var s29 := MStore(s28);
      assert s29.stack[9] == 0x64f;
      assert s29.stack[12] == 0x280;
      var s30 := Dup(s29, 3);
      assert s30.stack[10] == 0x64f;
      assert s30.stack[13] == 0x280;
      var s31 := Dup(s30, 5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s53(s31, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 122
    * Starting at 0x82b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x64f

    requires s0.stack[14] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Keccak256(s0);
      assert s1.stack[10] == 0x64f;
      assert s1.stack[13] == 0x280;
      var s2 := Dup(s1, 1);
      assert s2.stack[11] == 0x64f;
      assert s2.stack[14] == 0x280;
      var s3 := SLoad(s2);
      assert s3.stack[11] == 0x64f;
      assert s3.stack[14] == 0x280;
      var s4 := Dup(s3, 9);
      assert s4.stack[12] == 0x64f;
      assert s4.stack[15] == 0x280;
      var s5 := Dup(s4, 2);
      assert s5.stack[13] == 0x64f;
      assert s5.stack[16] == 0x280;
      var s6 := Sub(s5);
      assert s6.stack[12] == 0x64f;
      assert s6.stack[15] == 0x280;
      var s7 := Swap(s6, 1);
      assert s7.stack[12] == 0x64f;
      assert s7.stack[15] == 0x280;
      var s8 := Swap(s7, 2);
      assert s8.stack[12] == 0x64f;
      assert s8.stack[15] == 0x280;
      var s9 := SStore(s8);
      assert s9.stack[10] == 0x64f;
      assert s9.stack[13] == 0x280;
      var s10 := Swap(s9, 4);
      assert s10.stack[10] == 0x64f;
      assert s10.stack[13] == 0x280;
      var s11 := Dup(s10, 6);
      assert s11.stack[11] == 0x64f;
      assert s11.stack[14] == 0x280;
      var s12 := Swap(s11, 1);
      assert s12.stack[11] == 0x64f;
      assert s12.stack[14] == 0x280;
      var s13 := MStore(s12);
      assert s13.stack[9] == 0x64f;
      assert s13.stack[12] == 0x280;
      var s14 := Dup(s13, 2);
      assert s14.stack[10] == 0x64f;
      assert s14.stack[13] == 0x280;
      var s15 := SLoad(s14);
      assert s15.stack[10] == 0x64f;
      assert s15.stack[13] == 0x280;
      var s16 := Dup(s15, 8);
      assert s16.stack[11] == 0x64f;
      assert s16.stack[14] == 0x280;
      var s17 := Add(s16);
      assert s17.stack[10] == 0x64f;
      assert s17.stack[13] == 0x280;
      var s18 := Swap(s17, 1);
      assert s18.stack[10] == 0x64f;
      assert s18.stack[13] == 0x280;
      var s19 := Swap(s18, 2);
      assert s19.stack[10] == 0x64f;
      assert s19.stack[13] == 0x280;
      var s20 := SStore(s19);
      assert s20.stack[8] == 0x64f;
      assert s20.stack[11] == 0x280;
      var s21 := Swap(s20, 2);
      assert s21.stack[8] == 0x64f;
      assert s21.stack[11] == 0x280;
      var s22 := Swap(s21, 1);
      assert s22.stack[8] == 0x64f;
      assert s22.stack[11] == 0x280;
      var s23 := Swap(s22, 4);
      assert s23.stack[8] == 0x64f;
      assert s23.stack[11] == 0x280;
      var s24 := Add(s23);
      assert s24.stack[7] == 0x64f;
      assert s24.stack[10] == 0x280;
      var s25 := Swap(s24, 3);
      assert s25.stack[7] == 0x64f;
      assert s25.stack[10] == 0x280;
      var s26 := PushN(s25, 32, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      assert s26.stack[8] == 0x64f;
      assert s26.stack[11] == 0x280;
      var s27 := Swap(s26, 1);
      assert s27.stack[8] == 0x64f;
      assert s27.stack[11] == 0x280;
      var s28 := Dup(s27, 6);
      assert s28.stack[9] == 0x64f;
      assert s28.stack[12] == 0x280;
      var s29 := Swap(s28, 1);
      assert s29.stack[9] == 0x64f;
      assert s29.stack[12] == 0x280;
      var s30 := MLoad(s29);
      assert s30.stack[9] == 0x64f;
      assert s30.stack[12] == 0x280;
      var s31 := Swap(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s54(s31, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 123
    * Starting at 0x86a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x64f

    requires s0.stack[12] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[10] == 0x64f;
      assert s1.stack[13] == 0x280;
      var s2 := MStore(s1);
      assert s2.stack[8] == 0x64f;
      assert s2.stack[11] == 0x280;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[9] == 0x64f;
      assert s3.stack[12] == 0x280;
      var s4 := Add(s3);
      assert s4.stack[8] == 0x64f;
      assert s4.stack[11] == 0x280;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[9] == 0x64f;
      assert s5.stack[12] == 0x280;
      var s6 := MLoad(s5);
      assert s6.stack[9] == 0x64f;
      assert s6.stack[12] == 0x280;
      var s7 := Dup(s6, 1);
      assert s7.stack[10] == 0x64f;
      assert s7.stack[13] == 0x280;
      var s8 := Swap(s7, 2);
      assert s8.stack[10] == 0x64f;
      assert s8.stack[13] == 0x280;
      var s9 := Sub(s8);
      assert s9.stack[9] == 0x64f;
      assert s9.stack[12] == 0x280;
      var s10 := Swap(s9, 1);
      assert s10.stack[9] == 0x64f;
      assert s10.stack[12] == 0x280;
      var s11 := LogN(s10, 3);
      assert s11.stack[4] == 0x64f;
      assert s11.stack[7] == 0x280;
      var s12 := PushN(s11, 1, 0x01);
      assert s12.stack[5] == 0x64f;
      assert s12.stack[8] == 0x280;
      var s13 := PushN(s12, 1, 0xa0);
      assert s13.stack[6] == 0x64f;
      assert s13.stack[9] == 0x280;
      var s14 := PushN(s13, 1, 0x02);
      assert s14.stack[7] == 0x64f;
      assert s14.stack[10] == 0x280;
      var s15 := Exp(s14);
      assert s15.stack[6] == 0x64f;
      assert s15.stack[9] == 0x280;
      var s16 := Sub(s15);
      assert s16.stack[5] == 0x64f;
      assert s16.stack[8] == 0x280;
      var s17 := Dup(s16, 1);
      assert s17.stack[6] == 0x64f;
      assert s17.stack[9] == 0x280;
      var s18 := Dup(s17, 5);
      assert s18.stack[7] == 0x64f;
      assert s18.stack[10] == 0x280;
      var s19 := And(s18);
      assert s19.stack[6] == 0x64f;
      assert s19.stack[9] == 0x280;
      var s20 := PushN(s19, 1, 0x00);
      assert s20.stack[7] == 0x64f;
      assert s20.stack[10] == 0x280;
      var s21 := Swap(s20, 1);
      assert s21.stack[7] == 0x64f;
      assert s21.stack[10] == 0x280;
      var s22 := Dup(s21, 2);
      assert s22.stack[8] == 0x64f;
      assert s22.stack[11] == 0x280;
      var s23 := MStore(s22);
      assert s23.stack[6] == 0x64f;
      assert s23.stack[9] == 0x280;
      var s24 := PushN(s23, 1, 0x04);
      assert s24.stack[7] == 0x64f;
      assert s24.stack[10] == 0x280;
      var s25 := PushN(s24, 1, 0x20);
      assert s25.stack[8] == 0x64f;
      assert s25.stack[11] == 0x280;
      var s26 := MStore(s25);
      assert s26.stack[6] == 0x64f;
      assert s26.stack[9] == 0x280;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[7] == 0x64f;
      assert s27.stack[10] == 0x280;
      var s28 := Dup(s27, 1);
      assert s28.stack[8] == 0x64f;
      assert s28.stack[11] == 0x280;
      var s29 := Dup(s28, 3);
      assert s29.stack[9] == 0x64f;
      assert s29.stack[12] == 0x280;
      var s30 := Keccak256(s29);
      assert s30.stack[8] == 0x64f;
      assert s30.stack[11] == 0x280;
      var s31 := SLoad(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s55(s31, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 124
    * Starting at 0x892
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x892 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x64f

    requires s0.stack[11] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[8] == 0x64f;
      assert s1.stack[11] == 0x280;
      var s2 := Dup(s1, 8);
      assert s2.stack[9] == 0x64f;
      assert s2.stack[12] == 0x280;
      var s3 := And(s2);
      assert s3.stack[8] == 0x64f;
      assert s3.stack[11] == 0x280;
      var s4 := Dup(s3, 3);
      assert s4.stack[9] == 0x64f;
      assert s4.stack[12] == 0x280;
      var s5 := MStore(s4);
      assert s5.stack[7] == 0x64f;
      assert s5.stack[10] == 0x280;
      var s6 := Swap(s5, 1);
      assert s6.stack[7] == 0x64f;
      assert s6.stack[10] == 0x280;
      var s7 := Keccak256(s6);
      assert s7.stack[6] == 0x64f;
      assert s7.stack[9] == 0x280;
      var s8 := SLoad(s7);
      assert s8.stack[6] == 0x64f;
      assert s8.stack[9] == 0x280;
      var s9 := Add(s8);
      assert s9.stack[5] == 0x64f;
      assert s9.stack[8] == 0x280;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x64f;
      assert s10.stack[9] == 0x280;
      var s11 := Eq(s10);
      assert s11.stack[5] == 0x64f;
      assert s11.stack[8] == 0x280;
      var s12 := PushN(s11, 2, 0x08a2);
      assert s12.stack[0] == 0x8a2;
      assert s12.stack[6] == 0x64f;
      assert s12.stack[9] == 0x280;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s13, gas - 1)
      else
        ExecuteFromCFGNode_s56(s13, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 125
    * Starting at 0x8a1
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x64f

    requires s0.stack[7] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 57
    * Segment Id for this node is: 126
    * Starting at 0x8a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x64f

    requires s0.stack[7] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x64f;
      assert s1.stack[7] == 0x280;
      var s2 := Pop(s1);
      assert s2.stack[3] == 0x64f;
      assert s2.stack[6] == 0x280;
      var s3 := Pop(s2);
      assert s3.stack[2] == 0x64f;
      assert s3.stack[5] == 0x280;
      var s4 := Pop(s3);
      assert s4.stack[1] == 0x64f;
      assert s4.stack[4] == 0x280;
      var s5 := Pop(s4);
      assert s5.stack[0] == 0x64f;
      assert s5.stack[3] == 0x280;
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s6, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 98
    * Starting at 0x64f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x280

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x280;
      var s2 := Pop(s1);
      assert s2.stack[1] == 0x280;
      var s3 := Pop(s2);
      assert s3.stack[0] == 0x280;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s4, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 53
    * Starting at 0x280
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x280 as nat
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

  /** Node 60
    * Segment Id for this node is: 47
    * Starting at 0x24b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x0256);
      assert s4.stack[0] == 0x256;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s62(s5, gas - 1)
      else
        ExecuteFromCFGNode_s61(s5, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 48
    * Starting at 0x252
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x252 as nat
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

  /** Node 62
    * Segment Id for this node is: 49
    * Starting at 0x256
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x256 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x00d1);
      assert s2.stack[0] == 0xd1;
      var s3 := PushN(s2, 2, 0x05d9);
      assert s3.stack[0] == 0x5d9;
      assert s3.stack[1] == 0xd1;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s4, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 93
    * Starting at 0x5d9
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0xd1;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[1] == 0xd1;
      var s3 := Dup(s2, 1);
      assert s3.stack[2] == 0xd1;
      var s4 := SLoad(s3);
      assert s4.stack[2] == 0xd1;
      var s5 := PushN(s4, 1, 0x01);
      assert s5.stack[3] == 0xd1;
      var s6 := Dup(s5, 2);
      assert s6.stack[4] == 0xd1;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[5] == 0xd1;
      var s8 := And(s7);
      assert s8.stack[4] == 0xd1;
      var s9 := IsZero(s8);
      assert s9.stack[4] == 0xd1;
      var s10 := PushN(s9, 2, 0x0100);
      assert s10.stack[5] == 0xd1;
      var s11 := Mul(s10);
      assert s11.stack[4] == 0xd1;
      var s12 := Sub(s11);
      assert s12.stack[3] == 0xd1;
      var s13 := And(s12);
      assert s13.stack[2] == 0xd1;
      var s14 := PushN(s13, 1, 0x02);
      assert s14.stack[3] == 0xd1;
      var s15 := Swap(s14, 1);
      assert s15.stack[3] == 0xd1;
      var s16 := Div(s15);
      assert s16.stack[2] == 0xd1;
      var s17 := Dup(s16, 1);
      assert s17.stack[3] == 0xd1;
      var s18 := PushN(s17, 1, 0x1f);
      assert s18.stack[4] == 0xd1;
      var s19 := Add(s18);
      assert s19.stack[3] == 0xd1;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[4] == 0xd1;
      var s21 := Dup(s20, 1);
      assert s21.stack[5] == 0xd1;
      var s22 := Swap(s21, 2);
      assert s22.stack[5] == 0xd1;
      var s23 := Div(s22);
      assert s23.stack[4] == 0xd1;
      var s24 := Mul(s23);
      assert s24.stack[3] == 0xd1;
      var s25 := PushN(s24, 1, 0x20);
      assert s25.stack[4] == 0xd1;
      var s26 := Add(s25);
      assert s26.stack[3] == 0xd1;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[4] == 0xd1;
      var s28 := MLoad(s27);
      assert s28.stack[4] == 0xd1;
      var s29 := Swap(s28, 1);
      assert s29.stack[4] == 0xd1;
      var s30 := Dup(s29, 2);
      assert s30.stack[5] == 0xd1;
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s64(s31, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 94
    * Starting at 0x602
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x602 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[5] == 0xd1;
      var s2 := MStore(s1);
      assert s2.stack[3] == 0xd1;
      var s3 := Dup(s2, 1);
      assert s3.stack[4] == 0xd1;
      var s4 := Swap(s3, 3);
      assert s4.stack[4] == 0xd1;
      var s5 := Swap(s4, 2);
      assert s5.stack[4] == 0xd1;
      var s6 := Swap(s5, 1);
      assert s6.stack[4] == 0xd1;
      var s7 := Dup(s6, 2);
      assert s7.stack[5] == 0xd1;
      var s8 := Dup(s7, 2);
      assert s8.stack[6] == 0xd1;
      var s9 := MStore(s8);
      assert s9.stack[4] == 0xd1;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[5] == 0xd1;
      var s11 := Add(s10);
      assert s11.stack[4] == 0xd1;
      var s12 := Dup(s11, 3);
      assert s12.stack[5] == 0xd1;
      var s13 := Dup(s12, 1);
      assert s13.stack[6] == 0xd1;
      var s14 := SLoad(s13);
      assert s14.stack[6] == 0xd1;
      var s15 := PushN(s14, 1, 0x01);
      assert s15.stack[7] == 0xd1;
      var s16 := Dup(s15, 2);
      assert s16.stack[8] == 0xd1;
      var s17 := PushN(s16, 1, 0x01);
      assert s17.stack[9] == 0xd1;
      var s18 := And(s17);
      assert s18.stack[8] == 0xd1;
      var s19 := IsZero(s18);
      assert s19.stack[8] == 0xd1;
      var s20 := PushN(s19, 2, 0x0100);
      assert s20.stack[9] == 0xd1;
      var s21 := Mul(s20);
      assert s21.stack[8] == 0xd1;
      var s22 := Sub(s21);
      assert s22.stack[7] == 0xd1;
      var s23 := And(s22);
      assert s23.stack[6] == 0xd1;
      var s24 := PushN(s23, 1, 0x02);
      assert s24.stack[7] == 0xd1;
      var s25 := Swap(s24, 1);
      assert s25.stack[7] == 0xd1;
      var s26 := Div(s25);
      assert s26.stack[6] == 0xd1;
      var s27 := Dup(s26, 1);
      assert s27.stack[7] == 0xd1;
      var s28 := IsZero(s27);
      assert s28.stack[7] == 0xd1;
      var s29 := PushN(s28, 2, 0x03a2);
      assert s29.stack[0] == 0x3a2;
      assert s29.stack[8] == 0xd1;
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s30, gas - 1)
      else
        ExecuteFromCFGNode_s65(s30, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 95
    * Starting at 0x629
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x629 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[7] == 0xd1;
      var s2 := PushN(s1, 1, 0x1f);
      assert s2.stack[8] == 0xd1;
      var s3 := Lt(s2);
      assert s3.stack[7] == 0xd1;
      var s4 := PushN(s3, 2, 0x0377);
      assert s4.stack[0] == 0x377;
      assert s4.stack[8] == 0xd1;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s5, gas - 1)
      else
        ExecuteFromCFGNode_s66(s5, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 96
    * Starting at 0x631
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x631 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      assert s1.stack[7] == 0xd1;
      var s2 := Dup(s1, 1);
      assert s2.stack[8] == 0xd1;
      var s3 := Dup(s2, 4);
      assert s3.stack[9] == 0xd1;
      var s4 := SLoad(s3);
      assert s4.stack[9] == 0xd1;
      var s5 := Div(s4);
      assert s5.stack[8] == 0xd1;
      var s6 := Mul(s5);
      assert s6.stack[7] == 0xd1;
      var s7 := Dup(s6, 4);
      assert s7.stack[8] == 0xd1;
      var s8 := MStore(s7);
      assert s8.stack[6] == 0xd1;
      var s9 := Swap(s8, 2);
      assert s9.stack[6] == 0xd1;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[7] == 0xd1;
      var s11 := Add(s10);
      assert s11.stack[6] == 0xd1;
      var s12 := Swap(s11, 2);
      assert s12.stack[6] == 0xd1;
      var s13 := PushN(s12, 2, 0x03a2);
      assert s13.stack[0] == 0x3a2;
      assert s13.stack[7] == 0xd1;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s14, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 69
    * Starting at 0x3a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0xd1;
      var s2 := Pop(s1);
      assert s2.stack[5] == 0xd1;
      var s3 := Pop(s2);
      assert s3.stack[4] == 0xd1;
      var s4 := Pop(s3);
      assert s4.stack[3] == 0xd1;
      var s5 := Pop(s4);
      assert s5.stack[2] == 0xd1;
      var s6 := Pop(s5);
      assert s6.stack[1] == 0xd1;
      var s7 := Dup(s6, 2);
      assert s7.stack[0] == 0xd1;
      assert s7.stack[2] == 0xd1;
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s8, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 17
    * Starting at 0xd1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0xd1;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0xd1;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0xd1;
      var s4 := PushN(s3, 1, 0x20);
      assert s4.stack[3] == 0xd1;
      var s5 := Dup(s4, 1);
      assert s5.stack[4] == 0xd1;
      var s6 := Dup(s5, 3);
      assert s6.stack[5] == 0xd1;
      var s7 := MStore(s6);
      assert s7.stack[3] == 0xd1;
      var s8 := Dup(s7, 2);
      assert s8.stack[4] == 0xd1;
      var s9 := Swap(s8, 1);
      assert s9.stack[4] == 0xd1;
      var s10 := Dup(s9, 2);
      assert s10.stack[5] == 0xd1;
      var s11 := Add(s10);
      assert s11.stack[4] == 0xd1;
      var s12 := Dup(s11, 4);
      assert s12.stack[5] == 0xd1;
      var s13 := Dup(s12, 2);
      assert s13.stack[6] == 0xd1;
      var s14 := Dup(s13, 2);
      assert s14.stack[7] == 0xd1;
      var s15 := MLoad(s14);
      assert s15.stack[7] == 0xd1;
      var s16 := Dup(s15, 2);
      assert s16.stack[8] == 0xd1;
      var s17 := MStore(s16);
      assert s17.stack[6] == 0xd1;
      var s18 := PushN(s17, 1, 0x20);
      assert s18.stack[7] == 0xd1;
      var s19 := Add(s18);
      assert s19.stack[6] == 0xd1;
      var s20 := Swap(s19, 2);
      assert s20.stack[6] == 0xd1;
      var s21 := Pop(s20);
      assert s21.stack[5] == 0xd1;
      var s22 := Dup(s21, 1);
      assert s22.stack[6] == 0xd1;
      var s23 := MLoad(s22);
      assert s23.stack[6] == 0xd1;
      var s24 := Swap(s23, 1);
      assert s24.stack[6] == 0xd1;
      var s25 := PushN(s24, 1, 0x20);
      assert s25.stack[7] == 0xd1;
      var s26 := Add(s25);
      assert s26.stack[6] == 0xd1;
      var s27 := Swap(s26, 1);
      assert s27.stack[6] == 0xd1;
      var s28 := Dup(s27, 1);
      assert s28.stack[7] == 0xd1;
      var s29 := Dup(s28, 4);
      assert s29.stack[8] == 0xd1;
      var s30 := Dup(s29, 4);
      assert s30.stack[9] == 0xd1;
      var s31 := PushN(s30, 1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s69(s31, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 18
    * Starting at 0xf5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[10] == 0xd1;
      var s2 := Dup(s1, 4);
      assert s2.stack[11] == 0xd1;
      var s3 := Dup(s2, 2);
      assert s3.stack[12] == 0xd1;
      var s4 := Lt(s3);
      assert s4.stack[11] == 0xd1;
      var s5 := IsZero(s4);
      assert s5.stack[11] == 0xd1;
      var s6 := PushN(s5, 2, 0x010d);
      assert s6.stack[0] == 0x10d;
      assert s6.stack[12] == 0xd1;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s7, gas - 1)
      else
        ExecuteFromCFGNode_s70(s7, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 19
    * Starting at 0xfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[11] == 0xd1;
      var s2 := Dup(s1, 3);
      assert s2.stack[12] == 0xd1;
      var s3 := Add(s2);
      assert s3.stack[11] == 0xd1;
      var s4 := MLoad(s3);
      assert s4.stack[11] == 0xd1;
      var s5 := Dup(s4, 4);
      assert s5.stack[12] == 0xd1;
      var s6 := Dup(s5, 3);
      assert s6.stack[13] == 0xd1;
      var s7 := Add(s6);
      assert s7.stack[12] == 0xd1;
      var s8 := MStore(s7);
      assert s8.stack[10] == 0xd1;
      var s9 := PushN(s8, 1, 0x20);
      assert s9.stack[11] == 0xd1;
      var s10 := Add(s9);
      assert s10.stack[10] == 0xd1;
      var s11 := PushN(s10, 2, 0x00f5);
      assert s11.stack[0] == 0xf5;
      assert s11.stack[11] == 0xd1;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s12, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 20
    * Starting at 0x10d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[10] == 0xd1;
      var s2 := Pop(s1);
      assert s2.stack[9] == 0xd1;
      var s3 := Pop(s2);
      assert s3.stack[8] == 0xd1;
      var s4 := Pop(s3);
      assert s4.stack[7] == 0xd1;
      var s5 := Pop(s4);
      assert s5.stack[6] == 0xd1;
      var s6 := Swap(s5, 1);
      assert s6.stack[6] == 0xd1;
      var s7 := Pop(s6);
      assert s7.stack[5] == 0xd1;
      var s8 := Swap(s7, 1);
      assert s8.stack[5] == 0xd1;
      var s9 := Dup(s8, 2);
      assert s9.stack[6] == 0xd1;
      var s10 := Add(s9);
      assert s10.stack[5] == 0xd1;
      var s11 := Swap(s10, 1);
      assert s11.stack[5] == 0xd1;
      var s12 := PushN(s11, 1, 0x1f);
      assert s12.stack[6] == 0xd1;
      var s13 := And(s12);
      assert s13.stack[5] == 0xd1;
      var s14 := Dup(s13, 1);
      assert s14.stack[6] == 0xd1;
      var s15 := IsZero(s14);
      assert s15.stack[6] == 0xd1;
      var s16 := PushN(s15, 2, 0x013a);
      assert s16.stack[0] == 0x13a;
      assert s16.stack[7] == 0xd1;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s17, gas - 1)
      else
        ExecuteFromCFGNode_s72(s17, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 21
    * Starting at 0x121
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[6] == 0xd1;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0xd1;
      var s3 := Sub(s2);
      assert s3.stack[6] == 0xd1;
      var s4 := Dup(s3, 1);
      assert s4.stack[7] == 0xd1;
      var s5 := MLoad(s4);
      assert s5.stack[7] == 0xd1;
      var s6 := PushN(s5, 1, 0x01);
      assert s6.stack[8] == 0xd1;
      var s7 := Dup(s6, 4);
      assert s7.stack[9] == 0xd1;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[10] == 0xd1;
      var s9 := Sub(s8);
      assert s9.stack[9] == 0xd1;
      var s10 := PushN(s9, 2, 0x0100);
      assert s10.stack[10] == 0xd1;
      var s11 := Exp(s10);
      assert s11.stack[9] == 0xd1;
      var s12 := Sub(s11);
      assert s12.stack[8] == 0xd1;
      var s13 := Not(s12);
      assert s13.stack[8] == 0xd1;
      var s14 := And(s13);
      assert s14.stack[7] == 0xd1;
      var s15 := Dup(s14, 2);
      assert s15.stack[8] == 0xd1;
      var s16 := MStore(s15);
      assert s16.stack[6] == 0xd1;
      var s17 := PushN(s16, 1, 0x20);
      assert s17.stack[7] == 0xd1;
      var s18 := Add(s17);
      assert s18.stack[6] == 0xd1;
      var s19 := Swap(s18, 2);
      assert s19.stack[6] == 0xd1;
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s73(s20, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 22
    * Starting at 0x13a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[5] == 0xd1;
      var s2 := Pop(s1);
      assert s2.stack[4] == 0xd1;
      var s3 := Swap(s2, 3);
      assert s3.stack[4] == 0xd1;
      var s4 := Pop(s3);
      assert s4.stack[3] == 0xd1;
      var s5 := Pop(s4);
      assert s5.stack[2] == 0xd1;
      var s6 := Pop(s5);
      assert s6.stack[1] == 0xd1;
      var s7 := PushN(s6, 1, 0x40);
      assert s7.stack[2] == 0xd1;
      var s8 := MLoad(s7);
      assert s8.stack[2] == 0xd1;
      var s9 := Dup(s8, 1);
      assert s9.stack[3] == 0xd1;
      var s10 := Swap(s9, 2);
      assert s10.stack[3] == 0xd1;
      var s11 := Sub(s10);
      assert s11.stack[2] == 0xd1;
      var s12 := Swap(s11, 1);
      assert s12.stack[2] == 0xd1;
      var s13 := Return(s12);
      // Segment is terminal (Revert, Stop or Return)
      s13
  }

  /** Node 74
    * Segment Id for this node is: 66
    * Starting at 0x377
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x377 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0xd1;
      var s2 := Dup(s1, 3);
      assert s2.stack[7] == 0xd1;
      var s3 := Add(s2);
      assert s3.stack[6] == 0xd1;
      var s4 := Swap(s3, 2);
      assert s4.stack[6] == 0xd1;
      var s5 := Swap(s4, 1);
      assert s5.stack[6] == 0xd1;
      var s6 := PushN(s5, 1, 0x00);
      assert s6.stack[7] == 0xd1;
      var s7 := MStore(s6);
      assert s7.stack[5] == 0xd1;
      var s8 := PushN(s7, 1, 0x20);
      assert s8.stack[6] == 0xd1;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[7] == 0xd1;
      var s10 := Keccak256(s9);
      assert s10.stack[6] == 0xd1;
      var s11 := Swap(s10, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s75(s11, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 67
    * Starting at 0x385
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[6] == 0xd1;
      var s2 := Dup(s1, 2);
      assert s2.stack[7] == 0xd1;
      var s3 := SLoad(s2);
      assert s3.stack[7] == 0xd1;
      var s4 := Dup(s3, 2);
      assert s4.stack[8] == 0xd1;
      var s5 := MStore(s4);
      assert s5.stack[6] == 0xd1;
      var s6 := Swap(s5, 1);
      assert s6.stack[6] == 0xd1;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[7] == 0xd1;
      var s8 := Add(s7);
      assert s8.stack[6] == 0xd1;
      var s9 := Swap(s8, 1);
      assert s9.stack[6] == 0xd1;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[7] == 0xd1;
      var s11 := Add(s10);
      assert s11.stack[6] == 0xd1;
      var s12 := Dup(s11, 1);
      assert s12.stack[7] == 0xd1;
      var s13 := Dup(s12, 4);
      assert s13.stack[8] == 0xd1;
      var s14 := Gt(s13);
      assert s14.stack[7] == 0xd1;
      var s15 := PushN(s14, 2, 0x0385);
      assert s15.stack[0] == 0x385;
      assert s15.stack[8] == 0xd1;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s16, gas - 1)
      else
        ExecuteFromCFGNode_s76(s16, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 68
    * Starting at 0x399
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x399 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 3);
      assert s1.stack[7] == 0xd1;
      var s2 := Swap(s1, 1);
      assert s2.stack[7] == 0xd1;
      var s3 := Sub(s2);
      assert s3.stack[6] == 0xd1;
      var s4 := PushN(s3, 1, 0x1f);
      assert s4.stack[7] == 0xd1;
      var s5 := And(s4);
      assert s5.stack[6] == 0xd1;
      var s6 := Dup(s5, 3);
      assert s6.stack[7] == 0xd1;
      var s7 := Add(s6);
      assert s7.stack[6] == 0xd1;
      var s8 := Swap(s7, 2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s67(s8, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 44
    * Starting at 0x229
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x229 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x0234);
      assert s4.stack[0] == 0x234;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s5, gas - 1)
      else
        ExecuteFromCFGNode_s78(s5, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 45
    * Starting at 0x230
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x230 as nat
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

  /** Node 79
    * Segment Id for this node is: 46
    * Starting at 0x234
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x234 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x016a);
      assert s2.stack[0] == 0x16a;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[1] == 0x16a;
      var s4 := PushN(s3, 1, 0xa0);
      assert s4.stack[2] == 0x16a;
      var s5 := PushN(s4, 1, 0x02);
      assert s5.stack[3] == 0x16a;
      var s6 := Exp(s5);
      assert s6.stack[2] == 0x16a;
      var s7 := Sub(s6);
      assert s7.stack[1] == 0x16a;
      var s8 := PushN(s7, 1, 0x04);
      assert s8.stack[2] == 0x16a;
      var s9 := CallDataLoad(s8);
      assert s9.stack[2] == 0x16a;
      var s10 := And(s9);
      assert s10.stack[1] == 0x16a;
      var s11 := PushN(s10, 1, 0x24);
      assert s11.stack[2] == 0x16a;
      var s12 := CallDataLoad(s11);
      assert s12.stack[2] == 0x16a;
      var s13 := PushN(s12, 2, 0x04fd);
      assert s13.stack[0] == 0x4fd;
      assert s13.stack[3] == 0x16a;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s14, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 85
    * Starting at 0x4fd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[3] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[4] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[5] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[4] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[3] == 0x16a;
      var s7 := Dup(s6, 3);
      assert s7.stack[4] == 0x16a;
      var s8 := And(s7);
      assert s8.stack[3] == 0x16a;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[4] == 0x16a;
      var s10 := Swap(s9, 1);
      assert s10.stack[4] == 0x16a;
      var s11 := Dup(s10, 2);
      assert s11.stack[5] == 0x16a;
      var s12 := MStore(s11);
      assert s12.stack[3] == 0x16a;
      var s13 := PushN(s12, 1, 0x04);
      assert s13.stack[4] == 0x16a;
      var s14 := PushN(s13, 1, 0x20);
      assert s14.stack[5] == 0x16a;
      var s15 := MStore(s14);
      assert s15.stack[3] == 0x16a;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[4] == 0x16a;
      var s17 := Dup(s16, 2);
      assert s17.stack[5] == 0x16a;
      var s18 := Keccak256(s17);
      assert s18.stack[4] == 0x16a;
      var s19 := SLoad(s18);
      assert s19.stack[4] == 0x16a;
      var s20 := Dup(s19, 3);
      assert s20.stack[5] == 0x16a;
      var s21 := Swap(s20, 1);
      assert s21.stack[5] == 0x16a;
      var s22 := Lt(s21);
      assert s22.stack[4] == 0x16a;
      var s23 := IsZero(s22);
      assert s23.stack[4] == 0x16a;
      var s24 := PushN(s23, 2, 0x0523);
      assert s24.stack[0] == 0x523;
      assert s24.stack[5] == 0x16a;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s82(s25, gas - 1)
      else
        ExecuteFromCFGNode_s81(s25, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 86
    * Starting at 0x51f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[4] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[5] == 0x16a;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 82
    * Segment Id for this node is: 87
    * Starting at 0x523
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x523 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[4] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[5] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[6] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[5] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[4] == 0x16a;
      var s7 := Dup(s6, 1);
      assert s7.stack[5] == 0x16a;
      var s8 := Dup(s7, 5);
      assert s8.stack[6] == 0x16a;
      var s9 := And(s8);
      assert s9.stack[5] == 0x16a;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[6] == 0x16a;
      var s11 := Swap(s10, 1);
      assert s11.stack[6] == 0x16a;
      var s12 := Dup(s11, 2);
      assert s12.stack[7] == 0x16a;
      var s13 := MStore(s12);
      assert s13.stack[5] == 0x16a;
      var s14 := PushN(s13, 1, 0x05);
      assert s14.stack[6] == 0x16a;
      var s15 := PushN(s14, 1, 0x20);
      assert s15.stack[7] == 0x16a;
      var s16 := Swap(s15, 1);
      assert s16.stack[7] == 0x16a;
      var s17 := Dup(s16, 2);
      assert s17.stack[8] == 0x16a;
      var s18 := MStore(s17);
      assert s18.stack[6] == 0x16a;
      var s19 := PushN(s18, 1, 0x40);
      assert s19.stack[7] == 0x16a;
      var s20 := Dup(s19, 1);
      assert s20.stack[8] == 0x16a;
      var s21 := Dup(s20, 4);
      assert s21.stack[9] == 0x16a;
      var s22 := Keccak256(s21);
      assert s22.stack[8] == 0x16a;
      var s23 := Caller(s22);
      assert s23.stack[9] == 0x16a;
      var s24 := Swap(s23, 1);
      assert s24.stack[9] == 0x16a;
      var s25 := Swap(s24, 5);
      assert s25.stack[9] == 0x16a;
      var s26 := And(s25);
      assert s26.stack[8] == 0x16a;
      var s27 := Dup(s26, 4);
      assert s27.stack[9] == 0x16a;
      var s28 := MStore(s27);
      assert s28.stack[7] == 0x16a;
      var s29 := Swap(s28, 3);
      assert s29.stack[7] == 0x16a;
      var s30 := Swap(s29, 1);
      assert s30.stack[7] == 0x16a;
      var s31 := MStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s83(s31, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 88
    * Starting at 0x549
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x549 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Keccak256(s0);
      assert s1.stack[4] == 0x16a;
      var s2 := SLoad(s1);
      assert s2.stack[4] == 0x16a;
      var s3 := Dup(s2, 3);
      assert s3.stack[5] == 0x16a;
      var s4 := Gt(s3);
      assert s4.stack[4] == 0x16a;
      var s5 := IsZero(s4);
      assert s5.stack[4] == 0x16a;
      var s6 := PushN(s5, 2, 0x0556);
      assert s6.stack[0] == 0x556;
      assert s6.stack[5] == 0x16a;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s7, gas - 1)
      else
        ExecuteFromCFGNode_s84(s7, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 89
    * Starting at 0x552
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x552 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[4] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[5] == 0x16a;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 85
    * Segment Id for this node is: 90
    * Starting at 0x556
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x556 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[4] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[5] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[6] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[5] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[4] == 0x16a;
      var s7 := Dup(s6, 1);
      assert s7.stack[5] == 0x16a;
      var s8 := Dup(s7, 5);
      assert s8.stack[6] == 0x16a;
      var s9 := And(s8);
      assert s9.stack[5] == 0x16a;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[6] == 0x16a;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x16a;
      var s12 := Dup(s11, 2);
      assert s12.stack[8] == 0x16a;
      var s13 := MStore(s12);
      assert s13.stack[6] == 0x16a;
      var s14 := PushN(s13, 1, 0x04);
      assert s14.stack[7] == 0x16a;
      var s15 := PushN(s14, 1, 0x20);
      assert s15.stack[8] == 0x16a;
      var s16 := Swap(s15, 1);
      assert s16.stack[8] == 0x16a;
      var s17 := Dup(s16, 2);
      assert s17.stack[9] == 0x16a;
      var s18 := MStore(s17);
      assert s18.stack[7] == 0x16a;
      var s19 := PushN(s18, 1, 0x40);
      assert s19.stack[8] == 0x16a;
      var s20 := Dup(s19, 1);
      assert s20.stack[9] == 0x16a;
      var s21 := Dup(s20, 4);
      assert s21.stack[10] == 0x16a;
      var s22 := Keccak256(s21);
      assert s22.stack[9] == 0x16a;
      var s23 := Dup(s22, 1);
      assert s23.stack[10] == 0x16a;
      var s24 := SLoad(s23);
      assert s24.stack[10] == 0x16a;
      var s25 := Dup(s24, 9);
      assert s25.stack[11] == 0x16a;
      var s26 := Swap(s25, 1);
      assert s26.stack[11] == 0x16a;
      var s27 := Sub(s26);
      assert s27.stack[10] == 0x16a;
      var s28 := Swap(s27, 1);
      assert s28.stack[10] == 0x16a;
      var s29 := SStore(s28);
      assert s29.stack[8] == 0x16a;
      var s30 := PushN(s29, 1, 0x05);
      assert s30.stack[9] == 0x16a;
      var s31 := Dup(s30, 3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s86(s31, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 91
    * Starting at 0x57d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.stack[8] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[9] == 0x16a;
      var s3 := Dup(s2, 4);
      assert s3.stack[10] == 0x16a;
      var s4 := Keccak256(s3);
      assert s4.stack[9] == 0x16a;
      var s5 := Caller(s4);
      assert s5.stack[10] == 0x16a;
      var s6 := Swap(s5, 1);
      assert s6.stack[10] == 0x16a;
      var s7 := Swap(s6, 6);
      assert s7.stack[10] == 0x16a;
      var s8 := And(s7);
      assert s8.stack[9] == 0x16a;
      var s9 := Dup(s8, 4);
      assert s9.stack[10] == 0x16a;
      var s10 := MStore(s9);
      assert s10.stack[8] == 0x16a;
      var s11 := Swap(s10, 4);
      assert s11.stack[8] == 0x16a;
      var s12 := Swap(s11, 1);
      assert s12.stack[8] == 0x16a;
      var s13 := MStore(s12);
      assert s13.stack[6] == 0x16a;
      var s14 := Dup(s13, 3);
      assert s14.stack[7] == 0x16a;
      var s15 := Swap(s14, 1);
      assert s15.stack[7] == 0x16a;
      var s16 := Keccak256(s15);
      assert s16.stack[6] == 0x16a;
      var s17 := Dup(s16, 1);
      assert s17.stack[7] == 0x16a;
      var s18 := SLoad(s17);
      assert s18.stack[7] == 0x16a;
      var s19 := Dup(s18, 6);
      assert s19.stack[8] == 0x16a;
      var s20 := Swap(s19, 1);
      assert s20.stack[8] == 0x16a;
      var s21 := Sub(s20);
      assert s21.stack[7] == 0x16a;
      var s22 := Swap(s21, 1);
      assert s22.stack[7] == 0x16a;
      var s23 := SStore(s22);
      assert s23.stack[5] == 0x16a;
      var s24 := PushN(s23, 1, 0x03);
      assert s24.stack[6] == 0x16a;
      var s25 := Dup(s24, 1);
      assert s25.stack[7] == 0x16a;
      var s26 := SLoad(s25);
      assert s26.stack[7] == 0x16a;
      var s27 := Dup(s26, 6);
      assert s27.stack[8] == 0x16a;
      var s28 := Swap(s27, 1);
      assert s28.stack[8] == 0x16a;
      var s29 := Sub(s28);
      assert s29.stack[7] == 0x16a;
      var s30 := Swap(s29, 1);
      assert s30.stack[7] == 0x16a;
      var s31 := SStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s87(s31, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 92
    * Starting at 0x59d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[5] == 0x16a;
      var s2 := PushN(s1, 32, 0xcc16f5dbb4873280815c1ee09dbd06736cffcc184412cf7a71a0fdb75d397ca5);
      assert s2.stack[6] == 0x16a;
      var s3 := Swap(s2, 1);
      assert s3.stack[6] == 0x16a;
      var s4 := Dup(s3, 5);
      assert s4.stack[7] == 0x16a;
      var s5 := Swap(s4, 1);
      assert s5.stack[7] == 0x16a;
      var s6 := MLoad(s5);
      assert s6.stack[7] == 0x16a;
      var s7 := Swap(s6, 1);
      assert s7.stack[7] == 0x16a;
      var s8 := Dup(s7, 2);
      assert s8.stack[8] == 0x16a;
      var s9 := MStore(s8);
      assert s9.stack[6] == 0x16a;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[7] == 0x16a;
      var s11 := Add(s10);
      assert s11.stack[6] == 0x16a;
      var s12 := PushN(s11, 1, 0x40);
      assert s12.stack[7] == 0x16a;
      var s13 := MLoad(s12);
      assert s13.stack[7] == 0x16a;
      var s14 := Dup(s13, 1);
      assert s14.stack[8] == 0x16a;
      var s15 := Swap(s14, 2);
      assert s15.stack[8] == 0x16a;
      var s16 := Sub(s15);
      assert s16.stack[7] == 0x16a;
      var s17 := Swap(s16, 1);
      assert s17.stack[7] == 0x16a;
      var s18 := LogN(s17, 2);
      assert s18.stack[3] == 0x16a;
      var s19 := Pop(s18);
      assert s19.stack[2] == 0x16a;
      var s20 := PushN(s19, 1, 0x01);
      assert s20.stack[3] == 0x16a;
      var s21 := Swap(s20, 3);
      assert s21.stack[0] == 0x16a;
      var s22 := Swap(s21, 2);
      assert s22.stack[2] == 0x16a;
      var s23 := Pop(s22);
      assert s23.stack[1] == 0x16a;
      var s24 := Pop(s23);
      assert s24.stack[0] == 0x16a;
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s25, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 41
    * Starting at 0x20a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x0215);
      assert s4.stack[0] == 0x215;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s5, gas - 1)
      else
        ExecuteFromCFGNode_s89(s5, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 42
    * Starting at 0x211
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x211 as nat
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

  /** Node 90
    * Segment Id for this node is: 43
    * Starting at 0x215
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x215 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0191);
      assert s2.stack[0] == 0x191;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[1] == 0x191;
      var s4 := PushN(s3, 1, 0xa0);
      assert s4.stack[2] == 0x191;
      var s5 := PushN(s4, 1, 0x02);
      assert s5.stack[3] == 0x191;
      var s6 := Exp(s5);
      assert s6.stack[2] == 0x191;
      var s7 := Sub(s6);
      assert s7.stack[1] == 0x191;
      var s8 := PushN(s7, 1, 0x04);
      assert s8.stack[2] == 0x191;
      var s9 := CallDataLoad(s8);
      assert s9.stack[2] == 0x191;
      var s10 := And(s9);
      assert s10.stack[1] == 0x191;
      var s11 := PushN(s10, 2, 0x04eb);
      assert s11.stack[0] == 0x4eb;
      assert s11.stack[2] == 0x191;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s12, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 84
    * Starting at 0x4eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x191

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x191;
      var s2 := PushN(s1, 1, 0x04);
      assert s2.stack[2] == 0x191;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[3] == 0x191;
      var s4 := MStore(s3);
      assert s4.stack[1] == 0x191;
      var s5 := PushN(s4, 1, 0x00);
      assert s5.stack[2] == 0x191;
      var s6 := Swap(s5, 1);
      assert s6.stack[2] == 0x191;
      var s7 := Dup(s6, 2);
      assert s7.stack[3] == 0x191;
      var s8 := MStore(s7);
      assert s8.stack[1] == 0x191;
      var s9 := PushN(s8, 1, 0x40);
      assert s9.stack[2] == 0x191;
      var s10 := Swap(s9, 1);
      assert s10.stack[2] == 0x191;
      var s11 := Keccak256(s10);
      assert s11.stack[1] == 0x191;
      var s12 := SLoad(s11);
      assert s12.stack[1] == 0x191;
      var s13 := Dup(s12, 2);
      assert s13.stack[0] == 0x191;
      assert s13.stack[2] == 0x191;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s14, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 38
    * Starting at 0x1f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x01ff);
      assert s4.stack[0] == 0x1ff;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s5, gas - 1)
      else
        ExecuteFromCFGNode_s93(s5, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 39
    * Starting at 0x1fb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
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

  /** Node 94
    * Segment Id for this node is: 40
    * Starting at 0x1ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x016a);
      assert s2.stack[0] == 0x16a;
      var s3 := PushN(s2, 1, 0x04);
      assert s3.stack[1] == 0x16a;
      var s4 := CallDataLoad(s3);
      assert s4.stack[1] == 0x16a;
      var s5 := PushN(s4, 2, 0x0460);
      assert s5.stack[0] == 0x460;
      assert s5.stack[2] == 0x16a;
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s6, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 80
    * Starting at 0x460
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x460 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[2] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[3] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[4] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[3] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[2] == 0x16a;
      var s7 := Caller(s6);
      assert s7.stack[3] == 0x16a;
      var s8 := And(s7);
      assert s8.stack[2] == 0x16a;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[3] == 0x16a;
      var s10 := Swap(s9, 1);
      assert s10.stack[3] == 0x16a;
      var s11 := Dup(s10, 2);
      assert s11.stack[4] == 0x16a;
      var s12 := MStore(s11);
      assert s12.stack[2] == 0x16a;
      var s13 := PushN(s12, 1, 0x04);
      assert s13.stack[3] == 0x16a;
      var s14 := PushN(s13, 1, 0x20);
      assert s14.stack[4] == 0x16a;
      var s15 := MStore(s14);
      assert s15.stack[2] == 0x16a;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[3] == 0x16a;
      var s17 := Dup(s16, 2);
      assert s17.stack[4] == 0x16a;
      var s18 := Keccak256(s17);
      assert s18.stack[3] == 0x16a;
      var s19 := SLoad(s18);
      assert s19.stack[3] == 0x16a;
      var s20 := Dup(s19, 3);
      assert s20.stack[4] == 0x16a;
      var s21 := Swap(s20, 1);
      assert s21.stack[4] == 0x16a;
      var s22 := Lt(s21);
      assert s22.stack[3] == 0x16a;
      var s23 := IsZero(s22);
      assert s23.stack[3] == 0x16a;
      var s24 := PushN(s23, 2, 0x0486);
      assert s24.stack[0] == 0x486;
      assert s24.stack[4] == 0x16a;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s97(s25, gas - 1)
      else
        ExecuteFromCFGNode_s96(s25, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 81
    * Starting at 0x482
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x482 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[3] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[4] == 0x16a;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 97
    * Segment Id for this node is: 82
    * Starting at 0x486
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x486 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[3] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[4] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[5] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[4] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[3] == 0x16a;
      var s7 := Caller(s6);
      assert s7.stack[4] == 0x16a;
      var s8 := And(s7);
      assert s8.stack[3] == 0x16a;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[4] == 0x16a;
      var s10 := Dup(s9, 2);
      assert s10.stack[5] == 0x16a;
      var s11 := Dup(s10, 2);
      assert s11.stack[6] == 0x16a;
      var s12 := MStore(s11);
      assert s12.stack[4] == 0x16a;
      var s13 := PushN(s12, 1, 0x04);
      assert s13.stack[5] == 0x16a;
      var s14 := PushN(s13, 1, 0x20);
      assert s14.stack[6] == 0x16a;
      var s15 := MStore(s14);
      assert s15.stack[4] == 0x16a;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[5] == 0x16a;
      var s17 := Swap(s16, 1);
      assert s17.stack[5] == 0x16a;
      var s18 := Dup(s17, 2);
      assert s18.stack[6] == 0x16a;
      var s19 := Swap(s18, 1);
      assert s19.stack[6] == 0x16a;
      var s20 := Keccak256(s19);
      assert s20.stack[5] == 0x16a;
      var s21 := Dup(s20, 1);
      assert s21.stack[6] == 0x16a;
      var s22 := SLoad(s21);
      assert s22.stack[6] == 0x16a;
      var s23 := Dup(s22, 6);
      assert s23.stack[7] == 0x16a;
      var s24 := Swap(s23, 1);
      assert s24.stack[7] == 0x16a;
      var s25 := Sub(s24);
      assert s25.stack[6] == 0x16a;
      var s26 := Swap(s25, 1);
      assert s26.stack[6] == 0x16a;
      var s27 := SStore(s26);
      assert s27.stack[4] == 0x16a;
      var s28 := PushN(s27, 1, 0x03);
      assert s28.stack[5] == 0x16a;
      var s29 := Dup(s28, 1);
      assert s29.stack[6] == 0x16a;
      var s30 := SLoad(s29);
      assert s30.stack[6] == 0x16a;
      var s31 := Dup(s30, 6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s98(s31, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 83
    * Starting at 0x4ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[7] == 0x16a;
      var s2 := Sub(s1);
      assert s2.stack[6] == 0x16a;
      var s3 := Swap(s2, 1);
      assert s3.stack[6] == 0x16a;
      var s4 := SStore(s3);
      assert s4.stack[4] == 0x16a;
      var s5 := PushN(s4, 32, 0xcc16f5dbb4873280815c1ee09dbd06736cffcc184412cf7a71a0fdb75d397ca5);
      assert s5.stack[5] == 0x16a;
      var s6 := Swap(s5, 1);
      assert s6.stack[5] == 0x16a;
      var s7 := Dup(s6, 5);
      assert s7.stack[6] == 0x16a;
      var s8 := Swap(s7, 1);
      assert s8.stack[6] == 0x16a;
      var s9 := MLoad(s8);
      assert s9.stack[6] == 0x16a;
      var s10 := Swap(s9, 1);
      assert s10.stack[6] == 0x16a;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x16a;
      var s12 := MStore(s11);
      assert s12.stack[5] == 0x16a;
      var s13 := PushN(s12, 1, 0x20);
      assert s13.stack[6] == 0x16a;
      var s14 := Add(s13);
      assert s14.stack[5] == 0x16a;
      var s15 := PushN(s14, 1, 0x40);
      assert s15.stack[6] == 0x16a;
      var s16 := MLoad(s15);
      assert s16.stack[6] == 0x16a;
      var s17 := Dup(s16, 1);
      assert s17.stack[7] == 0x16a;
      var s18 := Swap(s17, 2);
      assert s18.stack[7] == 0x16a;
      var s19 := Sub(s18);
      assert s19.stack[6] == 0x16a;
      var s20 := Swap(s19, 1);
      assert s20.stack[6] == 0x16a;
      var s21 := LogN(s20, 2);
      assert s21.stack[2] == 0x16a;
      var s22 := Pop(s21);
      assert s22.stack[1] == 0x16a;
      var s23 := PushN(s22, 1, 0x01);
      assert s23.stack[2] == 0x16a;
      var s24 := Swap(s23, 2);
      assert s24.stack[0] == 0x16a;
      var s25 := Swap(s24, 1);
      assert s25.stack[1] == 0x16a;
      var s26 := Pop(s25);
      assert s26.stack[0] == 0x16a;
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s27, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 34
    * Starting at 0x1cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x01d6);
      assert s4.stack[0] == 0x1d6;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s5, gas - 1)
      else
        ExecuteFromCFGNode_s100(s5, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 35
    * Starting at 0x1d2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d2 as nat
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

  /** Node 101
    * Segment Id for this node is: 36
    * Starting at 0x1d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x01de);
      assert s2.stack[0] == 0x1de;
      var s3 := PushN(s2, 2, 0x0457);
      assert s3.stack[0] == 0x457;
      assert s3.stack[1] == 0x1de;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s4, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 79
    * Starting at 0x457
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1de

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0x1de;
      var s2 := PushN(s1, 1, 0x02);
      assert s2.stack[1] == 0x1de;
      var s3 := SLoad(s2);
      assert s3.stack[1] == 0x1de;
      var s4 := PushN(s3, 1, 0xff);
      assert s4.stack[2] == 0x1de;
      var s5 := And(s4);
      assert s5.stack[1] == 0x1de;
      var s6 := Dup(s5, 2);
      assert s6.stack[0] == 0x1de;
      assert s6.stack[2] == 0x1de;
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s7, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 37
    * Starting at 0x1de
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1de

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[1] == 0x1de;
      var s2 := PushN(s1, 1, 0x40);
      assert s2.stack[2] == 0x1de;
      var s3 := MLoad(s2);
      assert s3.stack[2] == 0x1de;
      var s4 := PushN(s3, 1, 0xff);
      assert s4.stack[3] == 0x1de;
      var s5 := Swap(s4, 1);
      assert s5.stack[3] == 0x1de;
      var s6 := Swap(s5, 2);
      assert s6.stack[3] == 0x1de;
      var s7 := And(s6);
      assert s7.stack[2] == 0x1de;
      var s8 := Dup(s7, 2);
      assert s8.stack[3] == 0x1de;
      var s9 := MStore(s8);
      assert s9.stack[1] == 0x1de;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[2] == 0x1de;
      var s11 := Add(s10);
      assert s11.stack[1] == 0x1de;
      var s12 := PushN(s11, 1, 0x40);
      assert s12.stack[2] == 0x1de;
      var s13 := MLoad(s12);
      assert s13.stack[2] == 0x1de;
      var s14 := Dup(s13, 1);
      assert s14.stack[3] == 0x1de;
      var s15 := Swap(s14, 2);
      assert s15.stack[3] == 0x1de;
      var s16 := Sub(s15);
      assert s16.stack[2] == 0x1de;
      var s17 := Swap(s16, 1);
      assert s17.stack[2] == 0x1de;
      var s18 := Return(s17);
      // Segment is terminal (Revert, Stop or Return)
      s18
  }

  /** Node 104
    * Segment Id for this node is: 31
    * Starting at 0x1a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x01ae);
      assert s4.stack[0] == 0x1ae;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s5, gas - 1)
      else
        ExecuteFromCFGNode_s105(s5, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 32
    * Starting at 0x1aa
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1aa as nat
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

  /** Node 106
    * Segment Id for this node is: 33
    * Starting at 0x1ae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x016a);
      assert s2.stack[0] == 0x16a;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[1] == 0x16a;
      var s4 := PushN(s3, 1, 0xa0);
      assert s4.stack[2] == 0x16a;
      var s5 := PushN(s4, 1, 0x02);
      assert s5.stack[3] == 0x16a;
      var s6 := Exp(s5);
      assert s6.stack[2] == 0x16a;
      var s7 := Sub(s6);
      assert s7.stack[1] == 0x16a;
      var s8 := PushN(s7, 1, 0x04);
      assert s8.stack[2] == 0x16a;
      var s9 := CallDataLoad(s8);
      assert s9.stack[2] == 0x16a;
      var s10 := Dup(s9, 2);
      assert s10.stack[3] == 0x16a;
      var s11 := And(s10);
      assert s11.stack[2] == 0x16a;
      var s12 := Swap(s11, 1);
      assert s12.stack[2] == 0x16a;
      var s13 := PushN(s12, 1, 0x24);
      assert s13.stack[3] == 0x16a;
      var s14 := CallDataLoad(s13);
      assert s14.stack[3] == 0x16a;
      var s15 := And(s14);
      assert s15.stack[2] == 0x16a;
      var s16 := PushN(s15, 1, 0x44);
      assert s16.stack[3] == 0x16a;
      var s17 := CallDataLoad(s16);
      assert s17.stack[3] == 0x16a;
      var s18 := PushN(s17, 2, 0x03e0);
      assert s18.stack[0] == 0x3e0;
      assert s18.stack[4] == 0x16a;
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s19, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 73
    * Starting at 0x3e0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[4] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[5] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[6] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[5] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[4] == 0x16a;
      var s7 := Dup(s6, 1);
      assert s7.stack[5] == 0x16a;
      var s8 := Dup(s7, 5);
      assert s8.stack[6] == 0x16a;
      var s9 := And(s8);
      assert s9.stack[5] == 0x16a;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[6] == 0x16a;
      var s11 := Swap(s10, 1);
      assert s11.stack[6] == 0x16a;
      var s12 := Dup(s11, 2);
      assert s12.stack[7] == 0x16a;
      var s13 := MStore(s12);
      assert s13.stack[5] == 0x16a;
      var s14 := PushN(s13, 1, 0x05);
      assert s14.stack[6] == 0x16a;
      var s15 := PushN(s14, 1, 0x20);
      assert s15.stack[7] == 0x16a;
      var s16 := Swap(s15, 1);
      assert s16.stack[7] == 0x16a;
      var s17 := Dup(s16, 2);
      assert s17.stack[8] == 0x16a;
      var s18 := MStore(s17);
      assert s18.stack[6] == 0x16a;
      var s19 := PushN(s18, 1, 0x40);
      assert s19.stack[7] == 0x16a;
      var s20 := Dup(s19, 1);
      assert s20.stack[8] == 0x16a;
      var s21 := Dup(s20, 4);
      assert s21.stack[9] == 0x16a;
      var s22 := Keccak256(s21);
      assert s22.stack[8] == 0x16a;
      var s23 := Caller(s22);
      assert s23.stack[9] == 0x16a;
      var s24 := Swap(s23, 1);
      assert s24.stack[9] == 0x16a;
      var s25 := Swap(s24, 5);
      assert s25.stack[9] == 0x16a;
      var s26 := And(s25);
      assert s26.stack[8] == 0x16a;
      var s27 := Dup(s26, 4);
      assert s27.stack[9] == 0x16a;
      var s28 := MStore(s27);
      assert s28.stack[7] == 0x16a;
      var s29 := Swap(s28, 3);
      assert s29.stack[7] == 0x16a;
      var s30 := Swap(s29, 1);
      assert s30.stack[7] == 0x16a;
      var s31 := MStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s108(s31, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 74
    * Starting at 0x406
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x406 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 1);
      assert s1.stack[5] == 0x16a;
      var s2 := Dup(s1, 2);
      assert s2.stack[6] == 0x16a;
      var s3 := Keccak256(s2);
      assert s3.stack[5] == 0x16a;
      var s4 := SLoad(s3);
      assert s4.stack[5] == 0x16a;
      var s5 := Dup(s4, 3);
      assert s5.stack[6] == 0x16a;
      var s6 := Gt(s5);
      assert s6.stack[5] == 0x16a;
      var s7 := IsZero(s6);
      assert s7.stack[5] == 0x16a;
      var s8 := PushN(s7, 2, 0x0415);
      assert s8.stack[0] == 0x415;
      assert s8.stack[6] == 0x16a;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s9, gas - 1)
      else
        ExecuteFromCFGNode_s109(s9, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 75
    * Starting at 0x411
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x411 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x16a;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 110
    * Segment Id for this node is: 76
    * Starting at 0x415
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x415 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[5] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[6] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[7] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[6] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[5] == 0x16a;
      var s7 := Dup(s6, 1);
      assert s7.stack[6] == 0x16a;
      var s8 := Dup(s7, 6);
      assert s8.stack[7] == 0x16a;
      var s9 := And(s8);
      assert s9.stack[6] == 0x16a;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[7] == 0x16a;
      var s11 := Swap(s10, 1);
      assert s11.stack[7] == 0x16a;
      var s12 := Dup(s11, 2);
      assert s12.stack[8] == 0x16a;
      var s13 := MStore(s12);
      assert s13.stack[6] == 0x16a;
      var s14 := PushN(s13, 1, 0x05);
      assert s14.stack[7] == 0x16a;
      var s15 := PushN(s14, 1, 0x20);
      assert s15.stack[8] == 0x16a;
      var s16 := Swap(s15, 1);
      assert s16.stack[8] == 0x16a;
      var s17 := Dup(s16, 2);
      assert s17.stack[9] == 0x16a;
      var s18 := MStore(s17);
      assert s18.stack[7] == 0x16a;
      var s19 := PushN(s18, 1, 0x40);
      assert s19.stack[8] == 0x16a;
      var s20 := Dup(s19, 1);
      assert s20.stack[9] == 0x16a;
      var s21 := Dup(s20, 4);
      assert s21.stack[10] == 0x16a;
      var s22 := Keccak256(s21);
      assert s22.stack[9] == 0x16a;
      var s23 := Caller(s22);
      assert s23.stack[10] == 0x16a;
      var s24 := Swap(s23, 1);
      assert s24.stack[10] == 0x16a;
      var s25 := Swap(s24, 5);
      assert s25.stack[10] == 0x16a;
      var s26 := And(s25);
      assert s26.stack[9] == 0x16a;
      var s27 := Dup(s26, 4);
      assert s27.stack[10] == 0x16a;
      var s28 := MStore(s27);
      assert s28.stack[8] == 0x16a;
      var s29 := Swap(s28, 3);
      assert s29.stack[8] == 0x16a;
      var s30 := Swap(s29, 1);
      assert s30.stack[8] == 0x16a;
      var s31 := MStore(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s111(s31, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 77
    * Starting at 0x43b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Keccak256(s0);
      assert s1.stack[5] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x16a;
      var s3 := SLoad(s2);
      assert s3.stack[6] == 0x16a;
      var s4 := Dup(s3, 4);
      assert s4.stack[7] == 0x16a;
      var s5 := Swap(s4, 1);
      assert s5.stack[7] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[6] == 0x16a;
      var s7 := Swap(s6, 1);
      assert s7.stack[6] == 0x16a;
      var s8 := SStore(s7);
      assert s8.stack[4] == 0x16a;
      var s9 := PushN(s8, 2, 0x044d);
      assert s9.stack[0] == 0x44d;
      assert s9.stack[5] == 0x16a;
      var s10 := Dup(s9, 5);
      assert s10.stack[1] == 0x44d;
      assert s10.stack[6] == 0x16a;
      var s11 := Dup(s10, 5);
      assert s11.stack[2] == 0x44d;
      assert s11.stack[7] == 0x16a;
      var s12 := Dup(s11, 5);
      assert s12.stack[3] == 0x44d;
      assert s12.stack[8] == 0x16a;
      var s13 := PushN(s12, 2, 0x07a2);
      assert s13.stack[0] == 0x7a2;
      assert s13.stack[4] == 0x44d;
      assert s13.stack[9] == 0x16a;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s14, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 115
    * Starting at 0x7a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x44d

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[3] == 0x44d;
      assert s1.stack[8] == 0x16a;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[4] == 0x44d;
      assert s2.stack[9] == 0x16a;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[5] == 0x44d;
      assert s3.stack[10] == 0x16a;
      var s4 := PushN(s3, 1, 0xa0);
      assert s4.stack[6] == 0x44d;
      assert s4.stack[11] == 0x16a;
      var s5 := PushN(s4, 1, 0x02);
      assert s5.stack[7] == 0x44d;
      assert s5.stack[12] == 0x16a;
      var s6 := Exp(s5);
      assert s6.stack[6] == 0x44d;
      assert s6.stack[11] == 0x16a;
      var s7 := Sub(s6);
      assert s7.stack[5] == 0x44d;
      assert s7.stack[10] == 0x16a;
      var s8 := Dup(s7, 4);
      assert s8.stack[6] == 0x44d;
      assert s8.stack[11] == 0x16a;
      var s9 := And(s8);
      assert s9.stack[5] == 0x44d;
      assert s9.stack[10] == 0x16a;
      var s10 := IsZero(s9);
      assert s10.stack[5] == 0x44d;
      assert s10.stack[10] == 0x16a;
      var s11 := IsZero(s10);
      assert s11.stack[5] == 0x44d;
      assert s11.stack[10] == 0x16a;
      var s12 := PushN(s11, 2, 0x07b9);
      assert s12.stack[0] == 0x7b9;
      assert s12.stack[6] == 0x44d;
      assert s12.stack[11] == 0x16a;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s13, gas - 1)
      else
        ExecuteFromCFGNode_s113(s13, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 116
    * Starting at 0x7b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x44d

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x44d;
      assert s1.stack[10] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x44d;
      assert s2.stack[11] == 0x16a;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 114
    * Segment Id for this node is: 117
    * Starting at 0x7b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x44d

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x44d;
      assert s1.stack[9] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[5] == 0x44d;
      assert s2.stack[10] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[6] == 0x44d;
      assert s3.stack[11] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[7] == 0x44d;
      assert s4.stack[12] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[6] == 0x44d;
      assert s5.stack[11] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[5] == 0x44d;
      assert s6.stack[10] == 0x16a;
      var s7 := Dup(s6, 5);
      assert s7.stack[6] == 0x44d;
      assert s7.stack[11] == 0x16a;
      var s8 := And(s7);
      assert s8.stack[5] == 0x44d;
      assert s8.stack[10] == 0x16a;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[6] == 0x44d;
      assert s9.stack[11] == 0x16a;
      var s10 := Swap(s9, 1);
      assert s10.stack[6] == 0x44d;
      assert s10.stack[11] == 0x16a;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x44d;
      assert s11.stack[12] == 0x16a;
      var s12 := MStore(s11);
      assert s12.stack[5] == 0x44d;
      assert s12.stack[10] == 0x16a;
      var s13 := PushN(s12, 1, 0x04);
      assert s13.stack[6] == 0x44d;
      assert s13.stack[11] == 0x16a;
      var s14 := PushN(s13, 1, 0x20);
      assert s14.stack[7] == 0x44d;
      assert s14.stack[12] == 0x16a;
      var s15 := MStore(s14);
      assert s15.stack[5] == 0x44d;
      assert s15.stack[10] == 0x16a;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[6] == 0x44d;
      assert s16.stack[11] == 0x16a;
      var s17 := Swap(s16, 1);
      assert s17.stack[6] == 0x44d;
      assert s17.stack[11] == 0x16a;
      var s18 := Keccak256(s17);
      assert s18.stack[5] == 0x44d;
      assert s18.stack[10] == 0x16a;
      var s19 := SLoad(s18);
      assert s19.stack[5] == 0x44d;
      assert s19.stack[10] == 0x16a;
      var s20 := Dup(s19, 3);
      assert s20.stack[6] == 0x44d;
      assert s20.stack[11] == 0x16a;
      var s21 := Swap(s20, 1);
      assert s21.stack[6] == 0x44d;
      assert s21.stack[11] == 0x16a;
      var s22 := Lt(s21);
      assert s22.stack[5] == 0x44d;
      assert s22.stack[10] == 0x16a;
      var s23 := IsZero(s22);
      assert s23.stack[5] == 0x44d;
      assert s23.stack[10] == 0x16a;
      var s24 := PushN(s23, 2, 0x07df);
      assert s24.stack[0] == 0x7df;
      assert s24.stack[6] == 0x44d;
      assert s24.stack[11] == 0x16a;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s116(s25, gas - 1)
      else
        ExecuteFromCFGNode_s115(s25, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 118
    * Starting at 0x7db
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x44d

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x44d;
      assert s1.stack[10] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x44d;
      assert s2.stack[11] == 0x16a;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 116
    * Segment Id for this node is: 119
    * Starting at 0x7df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x44d

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x44d;
      assert s1.stack[9] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[5] == 0x44d;
      assert s2.stack[10] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[6] == 0x44d;
      assert s3.stack[11] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[7] == 0x44d;
      assert s4.stack[12] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[6] == 0x44d;
      assert s5.stack[11] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[5] == 0x44d;
      assert s6.stack[10] == 0x16a;
      var s7 := Dup(s6, 4);
      assert s7.stack[6] == 0x44d;
      assert s7.stack[11] == 0x16a;
      var s8 := And(s7);
      assert s8.stack[5] == 0x44d;
      assert s8.stack[10] == 0x16a;
      var s9 := PushN(s8, 1, 0x00);
      assert s9.stack[6] == 0x44d;
      assert s9.stack[11] == 0x16a;
      var s10 := Swap(s9, 1);
      assert s10.stack[6] == 0x44d;
      assert s10.stack[11] == 0x16a;
      var s11 := Dup(s10, 2);
      assert s11.stack[7] == 0x44d;
      assert s11.stack[12] == 0x16a;
      var s12 := MStore(s11);
      assert s12.stack[5] == 0x44d;
      assert s12.stack[10] == 0x16a;
      var s13 := PushN(s12, 1, 0x04);
      assert s13.stack[6] == 0x44d;
      assert s13.stack[11] == 0x16a;
      var s14 := PushN(s13, 1, 0x20);
      assert s14.stack[7] == 0x44d;
      assert s14.stack[12] == 0x16a;
      var s15 := MStore(s14);
      assert s15.stack[5] == 0x44d;
      assert s15.stack[10] == 0x16a;
      var s16 := PushN(s15, 1, 0x40);
      assert s16.stack[6] == 0x44d;
      assert s16.stack[11] == 0x16a;
      var s17 := Swap(s16, 1);
      assert s17.stack[6] == 0x44d;
      assert s17.stack[11] == 0x16a;
      var s18 := Keccak256(s17);
      assert s18.stack[5] == 0x44d;
      assert s18.stack[10] == 0x16a;
      var s19 := SLoad(s18);
      assert s19.stack[5] == 0x44d;
      assert s19.stack[10] == 0x16a;
      var s20 := Dup(s19, 3);
      assert s20.stack[6] == 0x44d;
      assert s20.stack[11] == 0x16a;
      var s21 := Dup(s20, 2);
      assert s21.stack[7] == 0x44d;
      assert s21.stack[12] == 0x16a;
      var s22 := Add(s21);
      assert s22.stack[6] == 0x44d;
      assert s22.stack[11] == 0x16a;
      var s23 := Gt(s22);
      assert s23.stack[5] == 0x44d;
      assert s23.stack[10] == 0x16a;
      var s24 := PushN(s23, 2, 0x0805);
      assert s24.stack[0] == 0x805;
      assert s24.stack[6] == 0x44d;
      assert s24.stack[11] == 0x16a;
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s25, gas - 1)
      else
        ExecuteFromCFGNode_s117(s25, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 120
    * Starting at 0x801
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x801 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x44d

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      assert s1.stack[5] == 0x44d;
      assert s1.stack[10] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[6] == 0x44d;
      assert s2.stack[11] == 0x16a;
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 118
    * Segment Id for this node is: 121
    * Starting at 0x805
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x805 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x44d

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x44d;
      assert s1.stack[9] == 0x16a;
      var s2 := Pop(s1);
      assert s2.stack[3] == 0x44d;
      assert s2.stack[8] == 0x16a;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[4] == 0x44d;
      assert s3.stack[9] == 0x16a;
      var s4 := PushN(s3, 1, 0xa0);
      assert s4.stack[5] == 0x44d;
      assert s4.stack[10] == 0x16a;
      var s5 := PushN(s4, 1, 0x02);
      assert s5.stack[6] == 0x44d;
      assert s5.stack[11] == 0x16a;
      var s6 := Exp(s5);
      assert s6.stack[5] == 0x44d;
      assert s6.stack[10] == 0x16a;
      var s7 := Sub(s6);
      assert s7.stack[4] == 0x44d;
      assert s7.stack[9] == 0x16a;
      var s8 := Dup(s7, 1);
      assert s8.stack[5] == 0x44d;
      assert s8.stack[10] == 0x16a;
      var s9 := Dup(s8, 4);
      assert s9.stack[6] == 0x44d;
      assert s9.stack[11] == 0x16a;
      var s10 := And(s9);
      assert s10.stack[5] == 0x44d;
      assert s10.stack[10] == 0x16a;
      var s11 := PushN(s10, 1, 0x00);
      assert s11.stack[6] == 0x44d;
      assert s11.stack[11] == 0x16a;
      var s12 := Dup(s11, 2);
      assert s12.stack[7] == 0x44d;
      assert s12.stack[12] == 0x16a;
      var s13 := Dup(s12, 2);
      assert s13.stack[8] == 0x44d;
      assert s13.stack[13] == 0x16a;
      var s14 := MStore(s13);
      assert s14.stack[6] == 0x44d;
      assert s14.stack[11] == 0x16a;
      var s15 := PushN(s14, 1, 0x04);
      assert s15.stack[7] == 0x44d;
      assert s15.stack[12] == 0x16a;
      var s16 := PushN(s15, 1, 0x20);
      assert s16.stack[8] == 0x44d;
      assert s16.stack[13] == 0x16a;
      var s17 := MStore(s16);
      assert s17.stack[6] == 0x44d;
      assert s17.stack[11] == 0x16a;
      var s18 := PushN(s17, 1, 0x40);
      assert s18.stack[7] == 0x44d;
      assert s18.stack[12] == 0x16a;
      var s19 := Dup(s18, 1);
      assert s19.stack[8] == 0x44d;
      assert s19.stack[13] == 0x16a;
      var s20 := Dup(s19, 3);
      assert s20.stack[9] == 0x44d;
      assert s20.stack[14] == 0x16a;
      var s21 := Keccak256(s20);
      assert s21.stack[8] == 0x44d;
      assert s21.stack[13] == 0x16a;
      var s22 := Dup(s21, 1);
      assert s22.stack[9] == 0x44d;
      assert s22.stack[14] == 0x16a;
      var s23 := SLoad(s22);
      assert s23.stack[9] == 0x44d;
      assert s23.stack[14] == 0x16a;
      var s24 := Swap(s23, 5);
      assert s24.stack[9] == 0x44d;
      assert s24.stack[14] == 0x16a;
      var s25 := Dup(s24, 9);
      assert s25.stack[10] == 0x44d;
      assert s25.stack[15] == 0x16a;
      var s26 := And(s25);
      assert s26.stack[9] == 0x44d;
      assert s26.stack[14] == 0x16a;
      var s27 := Dup(s26, 1);
      assert s27.stack[10] == 0x44d;
      assert s27.stack[15] == 0x16a;
      var s28 := Dup(s27, 5);
      assert s28.stack[11] == 0x44d;
      assert s28.stack[16] == 0x16a;
      var s29 := MStore(s28);
      assert s29.stack[9] == 0x44d;
      assert s29.stack[14] == 0x16a;
      var s30 := Dup(s29, 3);
      assert s30.stack[10] == 0x44d;
      assert s30.stack[15] == 0x16a;
      var s31 := Dup(s30, 5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s119(s31, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 122
    * Starting at 0x82b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[11] == 0x44d

    requires s0.stack[16] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Keccak256(s0);
      assert s1.stack[10] == 0x44d;
      assert s1.stack[15] == 0x16a;
      var s2 := Dup(s1, 1);
      assert s2.stack[11] == 0x44d;
      assert s2.stack[16] == 0x16a;
      var s3 := SLoad(s2);
      assert s3.stack[11] == 0x44d;
      assert s3.stack[16] == 0x16a;
      var s4 := Dup(s3, 9);
      assert s4.stack[12] == 0x44d;
      assert s4.stack[17] == 0x16a;
      var s5 := Dup(s4, 2);
      assert s5.stack[13] == 0x44d;
      assert s5.stack[18] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[12] == 0x44d;
      assert s6.stack[17] == 0x16a;
      var s7 := Swap(s6, 1);
      assert s7.stack[12] == 0x44d;
      assert s7.stack[17] == 0x16a;
      var s8 := Swap(s7, 2);
      assert s8.stack[12] == 0x44d;
      assert s8.stack[17] == 0x16a;
      var s9 := SStore(s8);
      assert s9.stack[10] == 0x44d;
      assert s9.stack[15] == 0x16a;
      var s10 := Swap(s9, 4);
      assert s10.stack[10] == 0x44d;
      assert s10.stack[15] == 0x16a;
      var s11 := Dup(s10, 6);
      assert s11.stack[11] == 0x44d;
      assert s11.stack[16] == 0x16a;
      var s12 := Swap(s11, 1);
      assert s12.stack[11] == 0x44d;
      assert s12.stack[16] == 0x16a;
      var s13 := MStore(s12);
      assert s13.stack[9] == 0x44d;
      assert s13.stack[14] == 0x16a;
      var s14 := Dup(s13, 2);
      assert s14.stack[10] == 0x44d;
      assert s14.stack[15] == 0x16a;
      var s15 := SLoad(s14);
      assert s15.stack[10] == 0x44d;
      assert s15.stack[15] == 0x16a;
      var s16 := Dup(s15, 8);
      assert s16.stack[11] == 0x44d;
      assert s16.stack[16] == 0x16a;
      var s17 := Add(s16);
      assert s17.stack[10] == 0x44d;
      assert s17.stack[15] == 0x16a;
      var s18 := Swap(s17, 1);
      assert s18.stack[10] == 0x44d;
      assert s18.stack[15] == 0x16a;
      var s19 := Swap(s18, 2);
      assert s19.stack[10] == 0x44d;
      assert s19.stack[15] == 0x16a;
      var s20 := SStore(s19);
      assert s20.stack[8] == 0x44d;
      assert s20.stack[13] == 0x16a;
      var s21 := Swap(s20, 2);
      assert s21.stack[8] == 0x44d;
      assert s21.stack[13] == 0x16a;
      var s22 := Swap(s21, 1);
      assert s22.stack[8] == 0x44d;
      assert s22.stack[13] == 0x16a;
      var s23 := Swap(s22, 4);
      assert s23.stack[8] == 0x44d;
      assert s23.stack[13] == 0x16a;
      var s24 := Add(s23);
      assert s24.stack[7] == 0x44d;
      assert s24.stack[12] == 0x16a;
      var s25 := Swap(s24, 3);
      assert s25.stack[7] == 0x44d;
      assert s25.stack[12] == 0x16a;
      var s26 := PushN(s25, 32, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      assert s26.stack[8] == 0x44d;
      assert s26.stack[13] == 0x16a;
      var s27 := Swap(s26, 1);
      assert s27.stack[8] == 0x44d;
      assert s27.stack[13] == 0x16a;
      var s28 := Dup(s27, 6);
      assert s28.stack[9] == 0x44d;
      assert s28.stack[14] == 0x16a;
      var s29 := Swap(s28, 1);
      assert s29.stack[9] == 0x44d;
      assert s29.stack[14] == 0x16a;
      var s30 := MLoad(s29);
      assert s30.stack[9] == 0x44d;
      assert s30.stack[14] == 0x16a;
      var s31 := Swap(s30, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s120(s31, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 123
    * Starting at 0x86a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x44d

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[10] == 0x44d;
      assert s1.stack[15] == 0x16a;
      var s2 := MStore(s1);
      assert s2.stack[8] == 0x44d;
      assert s2.stack[13] == 0x16a;
      var s3 := PushN(s2, 1, 0x20);
      assert s3.stack[9] == 0x44d;
      assert s3.stack[14] == 0x16a;
      var s4 := Add(s3);
      assert s4.stack[8] == 0x44d;
      assert s4.stack[13] == 0x16a;
      var s5 := PushN(s4, 1, 0x40);
      assert s5.stack[9] == 0x44d;
      assert s5.stack[14] == 0x16a;
      var s6 := MLoad(s5);
      assert s6.stack[9] == 0x44d;
      assert s6.stack[14] == 0x16a;
      var s7 := Dup(s6, 1);
      assert s7.stack[10] == 0x44d;
      assert s7.stack[15] == 0x16a;
      var s8 := Swap(s7, 2);
      assert s8.stack[10] == 0x44d;
      assert s8.stack[15] == 0x16a;
      var s9 := Sub(s8);
      assert s9.stack[9] == 0x44d;
      assert s9.stack[14] == 0x16a;
      var s10 := Swap(s9, 1);
      assert s10.stack[9] == 0x44d;
      assert s10.stack[14] == 0x16a;
      var s11 := LogN(s10, 3);
      assert s11.stack[4] == 0x44d;
      assert s11.stack[9] == 0x16a;
      var s12 := PushN(s11, 1, 0x01);
      assert s12.stack[5] == 0x44d;
      assert s12.stack[10] == 0x16a;
      var s13 := PushN(s12, 1, 0xa0);
      assert s13.stack[6] == 0x44d;
      assert s13.stack[11] == 0x16a;
      var s14 := PushN(s13, 1, 0x02);
      assert s14.stack[7] == 0x44d;
      assert s14.stack[12] == 0x16a;
      var s15 := Exp(s14);
      assert s15.stack[6] == 0x44d;
      assert s15.stack[11] == 0x16a;
      var s16 := Sub(s15);
      assert s16.stack[5] == 0x44d;
      assert s16.stack[10] == 0x16a;
      var s17 := Dup(s16, 1);
      assert s17.stack[6] == 0x44d;
      assert s17.stack[11] == 0x16a;
      var s18 := Dup(s17, 5);
      assert s18.stack[7] == 0x44d;
      assert s18.stack[12] == 0x16a;
      var s19 := And(s18);
      assert s19.stack[6] == 0x44d;
      assert s19.stack[11] == 0x16a;
      var s20 := PushN(s19, 1, 0x00);
      assert s20.stack[7] == 0x44d;
      assert s20.stack[12] == 0x16a;
      var s21 := Swap(s20, 1);
      assert s21.stack[7] == 0x44d;
      assert s21.stack[12] == 0x16a;
      var s22 := Dup(s21, 2);
      assert s22.stack[8] == 0x44d;
      assert s22.stack[13] == 0x16a;
      var s23 := MStore(s22);
      assert s23.stack[6] == 0x44d;
      assert s23.stack[11] == 0x16a;
      var s24 := PushN(s23, 1, 0x04);
      assert s24.stack[7] == 0x44d;
      assert s24.stack[12] == 0x16a;
      var s25 := PushN(s24, 1, 0x20);
      assert s25.stack[8] == 0x44d;
      assert s25.stack[13] == 0x16a;
      var s26 := MStore(s25);
      assert s26.stack[6] == 0x44d;
      assert s26.stack[11] == 0x16a;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[7] == 0x44d;
      assert s27.stack[12] == 0x16a;
      var s28 := Dup(s27, 1);
      assert s28.stack[8] == 0x44d;
      assert s28.stack[13] == 0x16a;
      var s29 := Dup(s28, 3);
      assert s29.stack[9] == 0x44d;
      assert s29.stack[14] == 0x16a;
      var s30 := Keccak256(s29);
      assert s30.stack[8] == 0x44d;
      assert s30.stack[13] == 0x16a;
      var s31 := SLoad(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s121(s31, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 124
    * Starting at 0x892
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x892 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x44d

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap(s0, 3);
      assert s1.stack[8] == 0x44d;
      assert s1.stack[13] == 0x16a;
      var s2 := Dup(s1, 8);
      assert s2.stack[9] == 0x44d;
      assert s2.stack[14] == 0x16a;
      var s3 := And(s2);
      assert s3.stack[8] == 0x44d;
      assert s3.stack[13] == 0x16a;
      var s4 := Dup(s3, 3);
      assert s4.stack[9] == 0x44d;
      assert s4.stack[14] == 0x16a;
      var s5 := MStore(s4);
      assert s5.stack[7] == 0x44d;
      assert s5.stack[12] == 0x16a;
      var s6 := Swap(s5, 1);
      assert s6.stack[7] == 0x44d;
      assert s6.stack[12] == 0x16a;
      var s7 := Keccak256(s6);
      assert s7.stack[6] == 0x44d;
      assert s7.stack[11] == 0x16a;
      var s8 := SLoad(s7);
      assert s8.stack[6] == 0x44d;
      assert s8.stack[11] == 0x16a;
      var s9 := Add(s8);
      assert s9.stack[5] == 0x44d;
      assert s9.stack[10] == 0x16a;
      var s10 := Dup(s9, 2);
      assert s10.stack[6] == 0x44d;
      assert s10.stack[11] == 0x16a;
      var s11 := Eq(s10);
      assert s11.stack[5] == 0x44d;
      assert s11.stack[10] == 0x16a;
      var s12 := PushN(s11, 2, 0x08a2);
      assert s12.stack[0] == 0x8a2;
      assert s12.stack[6] == 0x44d;
      assert s12.stack[11] == 0x16a;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s13, gas - 1)
      else
        ExecuteFromCFGNode_s122(s13, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 125
    * Starting at 0x8a1
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x44d

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 123
    * Segment Id for this node is: 126
    * Starting at 0x8a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x44d

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x44d;
      assert s1.stack[9] == 0x16a;
      var s2 := Pop(s1);
      assert s2.stack[3] == 0x44d;
      assert s2.stack[8] == 0x16a;
      var s3 := Pop(s2);
      assert s3.stack[2] == 0x44d;
      assert s3.stack[7] == 0x16a;
      var s4 := Pop(s3);
      assert s4.stack[1] == 0x44d;
      assert s4.stack[6] == 0x16a;
      var s5 := Pop(s4);
      assert s5.stack[0] == 0x44d;
      assert s5.stack[5] == 0x16a;
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s6, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 78
    * Starting at 0x44d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[4] == 0x16a;
      var s2 := Pop(s1);
      assert s2.stack[3] == 0x16a;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[4] == 0x16a;
      var s4 := Swap(s3, 4);
      assert s4.stack[0] == 0x16a;
      var s5 := Swap(s4, 3);
      assert s5.stack[3] == 0x16a;
      var s6 := Pop(s5);
      assert s6.stack[2] == 0x16a;
      var s7 := Pop(s6);
      assert s7.stack[1] == 0x16a;
      var s8 := Pop(s7);
      assert s8.stack[0] == 0x16a;
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s9, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 27
    * Starting at 0x17e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x0189);
      assert s4.stack[0] == 0x189;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s5, gas - 1)
      else
        ExecuteFromCFGNode_s126(s5, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 28
    * Starting at 0x185
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x185 as nat
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

  /** Node 127
    * Segment Id for this node is: 29
    * Starting at 0x189
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x189 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0191);
      assert s2.stack[0] == 0x191;
      var s3 := PushN(s2, 2, 0x03da);
      assert s3.stack[0] == 0x3da;
      assert s3.stack[1] == 0x191;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s4, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 72
    * Starting at 0x3da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x191

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0x191;
      var s2 := PushN(s1, 1, 0x03);
      assert s2.stack[1] == 0x191;
      var s3 := SLoad(s2);
      assert s3.stack[1] == 0x191;
      var s4 := Dup(s3, 2);
      assert s4.stack[0] == 0x191;
      assert s4.stack[2] == 0x191;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s5, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 23
    * Starting at 0x148
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x148 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x0153);
      assert s4.stack[0] == 0x153;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s5, gas - 1)
      else
        ExecuteFromCFGNode_s130(s5, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 24
    * Starting at 0x14f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f as nat
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

  /** Node 131
    * Segment Id for this node is: 25
    * Starting at 0x153
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x016a);
      assert s2.stack[0] == 0x16a;
      var s3 := PushN(s2, 1, 0x01);
      assert s3.stack[1] == 0x16a;
      var s4 := PushN(s3, 1, 0xa0);
      assert s4.stack[2] == 0x16a;
      var s5 := PushN(s4, 1, 0x02);
      assert s5.stack[3] == 0x16a;
      var s6 := Exp(s5);
      assert s6.stack[2] == 0x16a;
      var s7 := Sub(s6);
      assert s7.stack[1] == 0x16a;
      var s8 := PushN(s7, 1, 0x04);
      assert s8.stack[2] == 0x16a;
      var s9 := CallDataLoad(s8);
      assert s9.stack[2] == 0x16a;
      var s10 := And(s9);
      assert s10.stack[1] == 0x16a;
      var s11 := PushN(s10, 1, 0x24);
      assert s11.stack[2] == 0x16a;
      var s12 := CallDataLoad(s11);
      assert s12.stack[2] == 0x16a;
      var s13 := PushN(s12, 2, 0x03aa);
      assert s13.stack[0] == 0x3aa;
      assert s13.stack[3] == 0x16a;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s14, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 70
    * Starting at 0x3aa
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[2] == 0x16a;
      var s2 := PushN(s1, 1, 0x01);
      assert s2.stack[3] == 0x16a;
      var s3 := PushN(s2, 1, 0xa0);
      assert s3.stack[4] == 0x16a;
      var s4 := PushN(s3, 1, 0x02);
      assert s4.stack[5] == 0x16a;
      var s5 := Exp(s4);
      assert s5.stack[4] == 0x16a;
      var s6 := Sub(s5);
      assert s6.stack[3] == 0x16a;
      var s7 := Caller(s6);
      assert s7.stack[4] == 0x16a;
      var s8 := Dup(s7, 2);
      assert s8.stack[5] == 0x16a;
      var s9 := And(s8);
      assert s9.stack[4] == 0x16a;
      var s10 := PushN(s9, 1, 0x00);
      assert s10.stack[5] == 0x16a;
      var s11 := Swap(s10, 1);
      assert s11.stack[5] == 0x16a;
      var s12 := Dup(s11, 2);
      assert s12.stack[6] == 0x16a;
      var s13 := MStore(s12);
      assert s13.stack[4] == 0x16a;
      var s14 := PushN(s13, 1, 0x05);
      assert s14.stack[5] == 0x16a;
      var s15 := PushN(s14, 1, 0x20);
      assert s15.stack[6] == 0x16a;
      var s16 := Swap(s15, 1);
      assert s16.stack[6] == 0x16a;
      var s17 := Dup(s16, 2);
      assert s17.stack[7] == 0x16a;
      var s18 := MStore(s17);
      assert s18.stack[5] == 0x16a;
      var s19 := PushN(s18, 1, 0x40);
      assert s19.stack[6] == 0x16a;
      var s20 := Dup(s19, 1);
      assert s20.stack[7] == 0x16a;
      var s21 := Dup(s20, 4);
      assert s21.stack[8] == 0x16a;
      var s22 := Keccak256(s21);
      assert s22.stack[7] == 0x16a;
      var s23 := Swap(s22, 4);
      assert s23.stack[7] == 0x16a;
      var s24 := Dup(s23, 7);
      assert s24.stack[8] == 0x16a;
      var s25 := And(s24);
      assert s25.stack[7] == 0x16a;
      var s26 := Dup(s25, 4);
      assert s26.stack[8] == 0x16a;
      var s27 := MStore(s26);
      assert s27.stack[6] == 0x16a;
      var s28 := Swap(s27, 3);
      assert s28.stack[6] == 0x16a;
      var s29 := Swap(s28, 1);
      assert s29.stack[6] == 0x16a;
      var s30 := MStore(s29);
      assert s30.stack[4] == 0x16a;
      var s31 := Keccak256(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s133(s31, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 71
    * Starting at 0x3d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      assert s1.stack[4] == 0x16a;
      var s2 := Swap(s1, 1);
      assert s2.stack[4] == 0x16a;
      var s3 := SStore(s2);
      assert s3.stack[2] == 0x16a;
      var s4 := PushN(s3, 1, 0x01);
      assert s4.stack[3] == 0x16a;
      var s5 := Swap(s4, 3);
      assert s5.stack[0] == 0x16a;
      var s6 := Swap(s5, 2);
      assert s6.stack[2] == 0x16a;
      var s7 := Pop(s6);
      assert s7.stack[1] == 0x16a;
      var s8 := Pop(s7);
      assert s8.stack[0] == 0x16a;
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s9, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 14
    * Starting at 0xbe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := PushN(s3, 2, 0x00c9);
      assert s4.stack[0] == 0xc9;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s5, gas - 1)
      else
        ExecuteFromCFGNode_s135(s5, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 15
    * Starting at 0xc5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5 as nat
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

  /** Node 136
    * Segment Id for this node is: 16
    * Starting at 0xc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x00d1);
      assert s2.stack[0] == 0xd1;
      var s3 := PushN(s2, 2, 0x030c);
      assert s3.stack[0] == 0x30c;
      assert s3.stack[1] == 0xd1;
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s4, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 62
    * Starting at 0x30c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.stack[0] == 0xd1;
      var s2 := PushN(s1, 1, 0x00);
      assert s2.stack[1] == 0xd1;
      var s3 := Dup(s2, 1);
      assert s3.stack[2] == 0xd1;
      var s4 := SLoad(s3);
      assert s4.stack[2] == 0xd1;
      var s5 := PushN(s4, 1, 0x01);
      assert s5.stack[3] == 0xd1;
      var s6 := Dup(s5, 2);
      assert s6.stack[4] == 0xd1;
      var s7 := PushN(s6, 1, 0x01);
      assert s7.stack[5] == 0xd1;
      var s8 := And(s7);
      assert s8.stack[4] == 0xd1;
      var s9 := IsZero(s8);
      assert s9.stack[4] == 0xd1;
      var s10 := PushN(s9, 2, 0x0100);
      assert s10.stack[5] == 0xd1;
      var s11 := Mul(s10);
      assert s11.stack[4] == 0xd1;
      var s12 := Sub(s11);
      assert s12.stack[3] == 0xd1;
      var s13 := And(s12);
      assert s13.stack[2] == 0xd1;
      var s14 := PushN(s13, 1, 0x02);
      assert s14.stack[3] == 0xd1;
      var s15 := Swap(s14, 1);
      assert s15.stack[3] == 0xd1;
      var s16 := Div(s15);
      assert s16.stack[2] == 0xd1;
      var s17 := Dup(s16, 1);
      assert s17.stack[3] == 0xd1;
      var s18 := PushN(s17, 1, 0x1f);
      assert s18.stack[4] == 0xd1;
      var s19 := Add(s18);
      assert s19.stack[3] == 0xd1;
      var s20 := PushN(s19, 1, 0x20);
      assert s20.stack[4] == 0xd1;
      var s21 := Dup(s20, 1);
      assert s21.stack[5] == 0xd1;
      var s22 := Swap(s21, 2);
      assert s22.stack[5] == 0xd1;
      var s23 := Div(s22);
      assert s23.stack[4] == 0xd1;
      var s24 := Mul(s23);
      assert s24.stack[3] == 0xd1;
      var s25 := PushN(s24, 1, 0x20);
      assert s25.stack[4] == 0xd1;
      var s26 := Add(s25);
      assert s26.stack[3] == 0xd1;
      var s27 := PushN(s26, 1, 0x40);
      assert s27.stack[4] == 0xd1;
      var s28 := MLoad(s27);
      assert s28.stack[4] == 0xd1;
      var s29 := Swap(s28, 1);
      assert s29.stack[4] == 0xd1;
      var s30 := Dup(s29, 2);
      assert s30.stack[5] == 0xd1;
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s138(s31, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 63
    * Starting at 0x335
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x335 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x40);
      assert s1.stack[5] == 0xd1;
      var s2 := MStore(s1);
      assert s2.stack[3] == 0xd1;
      var s3 := Dup(s2, 1);
      assert s3.stack[4] == 0xd1;
      var s4 := Swap(s3, 3);
      assert s4.stack[4] == 0xd1;
      var s5 := Swap(s4, 2);
      assert s5.stack[4] == 0xd1;
      var s6 := Swap(s5, 1);
      assert s6.stack[4] == 0xd1;
      var s7 := Dup(s6, 2);
      assert s7.stack[5] == 0xd1;
      var s8 := Dup(s7, 2);
      assert s8.stack[6] == 0xd1;
      var s9 := MStore(s8);
      assert s9.stack[4] == 0xd1;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[5] == 0xd1;
      var s11 := Add(s10);
      assert s11.stack[4] == 0xd1;
      var s12 := Dup(s11, 3);
      assert s12.stack[5] == 0xd1;
      var s13 := Dup(s12, 1);
      assert s13.stack[6] == 0xd1;
      var s14 := SLoad(s13);
      assert s14.stack[6] == 0xd1;
      var s15 := PushN(s14, 1, 0x01);
      assert s15.stack[7] == 0xd1;
      var s16 := Dup(s15, 2);
      assert s16.stack[8] == 0xd1;
      var s17 := PushN(s16, 1, 0x01);
      assert s17.stack[9] == 0xd1;
      var s18 := And(s17);
      assert s18.stack[8] == 0xd1;
      var s19 := IsZero(s18);
      assert s19.stack[8] == 0xd1;
      var s20 := PushN(s19, 2, 0x0100);
      assert s20.stack[9] == 0xd1;
      var s21 := Mul(s20);
      assert s21.stack[8] == 0xd1;
      var s22 := Sub(s21);
      assert s22.stack[7] == 0xd1;
      var s23 := And(s22);
      assert s23.stack[6] == 0xd1;
      var s24 := PushN(s23, 1, 0x02);
      assert s24.stack[7] == 0xd1;
      var s25 := Swap(s24, 1);
      assert s25.stack[7] == 0xd1;
      var s26 := Div(s25);
      assert s26.stack[6] == 0xd1;
      var s27 := Dup(s26, 1);
      assert s27.stack[7] == 0xd1;
      var s28 := IsZero(s27);
      assert s28.stack[7] == 0xd1;
      var s29 := PushN(s28, 2, 0x03a2);
      assert s29.stack[0] == 0x3a2;
      assert s29.stack[8] == 0xd1;
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s30, gas - 1)
      else
        ExecuteFromCFGNode_s139(s30, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 64
    * Starting at 0x35c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 1);
      assert s1.stack[7] == 0xd1;
      var s2 := PushN(s1, 1, 0x1f);
      assert s2.stack[8] == 0xd1;
      var s3 := Lt(s2);
      assert s3.stack[7] == 0xd1;
      var s4 := PushN(s3, 2, 0x0377);
      assert s4.stack[0] == 0x377;
      assert s4.stack[8] == 0xd1;
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s5, gas - 1)
      else
        ExecuteFromCFGNode_s140(s5, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 65
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xd1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      assert s1.stack[7] == 0xd1;
      var s2 := Dup(s1, 1);
      assert s2.stack[8] == 0xd1;
      var s3 := Dup(s2, 4);
      assert s3.stack[9] == 0xd1;
      var s4 := SLoad(s3);
      assert s4.stack[9] == 0xd1;
      var s5 := Div(s4);
      assert s5.stack[8] == 0xd1;
      var s6 := Mul(s5);
      assert s6.stack[7] == 0xd1;
      var s7 := Dup(s6, 4);
      assert s7.stack[8] == 0xd1;
      var s8 := MStore(s7);
      assert s8.stack[6] == 0xd1;
      var s9 := Swap(s8, 2);
      assert s9.stack[6] == 0xd1;
      var s10 := PushN(s9, 1, 0x20);
      assert s10.stack[7] == 0xd1;
      var s11 := Add(s10);
      assert s11.stack[6] == 0xd1;
      var s12 := Swap(s11, 2);
      assert s12.stack[6] == 0xd1;
      var s13 := PushN(s12, 2, 0x03a2);
      assert s13.stack[0] == 0x3a2;
      assert s13.stack[7] == 0xd1;
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s14, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 13
    * Starting at 0xb9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
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
