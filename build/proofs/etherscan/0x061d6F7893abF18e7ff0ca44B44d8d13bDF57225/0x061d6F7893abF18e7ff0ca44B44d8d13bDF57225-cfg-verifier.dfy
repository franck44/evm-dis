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
      var s7 := Push2(s6, 0x000f);
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
      var s1 := Push0(s0);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0xf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf as nat
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
      var s6 := Push2(s5, 0x00b2);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s660(s7, gas - 1)
      else
        ExecuteFromCFGNode_s3(s7, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x19
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19 as nat
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
      var s6 := Push4(s5, 0x95d89b41);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x006f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s359(s9, gas - 1)
      else
        ExecuteFromCFGNode_s4(s9, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x29
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01a0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s321(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x34
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01be);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s232(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xae5e5451);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01ee);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s173(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x4a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xb8c9d25c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x020a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x55
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0228);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s96(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x60
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xe559d86a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0258);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 10
    * Starting at 0x6b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00b2);
      assert s1.Peek(0) == 0xb2;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s2, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 17
    * Starting at 0xb2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

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

  /** Node 12
    * Segment Id for this node is: 56
    * Starting at 0x258
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x258 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0272);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x026d);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x26d;
      assert s11.Peek(3) == 0x272;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0fe5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s14, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 215
    * Starting at 0xfe5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x26d

    requires s0.stack[3] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x26d;
      assert s1.Peek(3) == 0x272;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ffa);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s10, gas - 1)
      else
        ExecuteFromCFGNode_s14(s10, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 216
    * Starting at 0xff2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x26d

    requires s0.stack[4] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ff9);
      assert s1.Peek(0) == 0xff9;
      assert s1.Peek(4) == 0x26d;
      assert s1.Peek(5) == 0x272;
      var s2 := Push2(s1, 0x0da6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s3, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 156
    * Starting at 0xda6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0xff9

    requires s0.stack[4] == 0x26d

    requires s0.stack[5] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xff9;
      assert s1.Peek(4) == 0x26d;
      assert s1.Peek(5) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 16
    * Segment Id for this node is: 218
    * Starting at 0xffa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x26d

    requires s0.stack[4] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x26d;
      assert s1.Peek(4) == 0x272;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1007);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0e23);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s9, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 171
    * Starting at 0xe23
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x1007

    requires s0.stack[7] == 0x26d

    requires s0.stack[8] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1007;
      assert s1.Peek(7) == 0x26d;
      assert s1.Peek(8) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0e31);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0e0d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s10, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 167
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0x1007

    requires s0.stack[10] == 0x26d

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe31;
      assert s1.Peek(5) == 0x1007;
      assert s1.Peek(10) == 0x26d;
      assert s1.Peek(11) == 0x272;
      var s2 := Push2(s1, 0x0e16);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s5, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xe16

    requires s0.stack[3] == 0xe31

    requires s0.stack[7] == 0x1007

    requires s0.stack[12] == 0x26d

    requires s0.stack[13] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe16;
      assert s1.Peek(3) == 0xe31;
      assert s1.Peek(7) == 0x1007;
      assert s1.Peek(12) == 0x26d;
      assert s1.Peek(13) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s9, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 168
    * Starting at 0xe16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xe31

    requires s0.stack[6] == 0x1007

    requires s0.stack[11] == 0x26d

    requires s0.stack[12] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe31;
      assert s1.Peek(6) == 0x1007;
      assert s1.Peek(11) == 0x26d;
      assert s1.Peek(12) == 0x272;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0e20);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s5, gas - 1)
      else
        ExecuteFromCFGNode_s21(s5, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 169
    * Starting at 0xe1d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0x1007

    requires s0.stack[10] == 0x26d

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xe31;
      assert s1.Peek(6) == 0x1007;
      assert s1.Peek(11) == 0x26d;
      assert s1.Peek(12) == 0x272;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 22
    * Segment Id for this node is: 170
    * Starting at 0xe20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0x1007

    requires s0.stack[10] == 0x26d

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe31;
      assert s1.Peek(5) == 0x1007;
      assert s1.Peek(10) == 0x26d;
      assert s1.Peek(11) == 0x272;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s3, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 172
    * Starting at 0xe31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x1007

    requires s0.stack[8] == 0x26d

    requires s0.stack[9] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1007;
      assert s1.Peek(8) == 0x26d;
      assert s1.Peek(9) == 0x272;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s6, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 219
    * Starting at 0x1007
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1007 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x26d

    requires s0.stack[6] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x26d;
      assert s1.Peek(6) == 0x272;
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
    * Segment Id for this node is: 57
    * Starting at 0x26d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x272;
      var s2 := Push2(s1, 0x06f4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s3, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 104
    * Starting at 0x6f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x272;
      var s2 := Caller(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Push1(s4, 0x03);
      var s6 := Push0(s5);
      var s7 := Swap1(s6);
      var s8 := SLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0100);
      var s11 := Exp(s10);
      assert s11.Peek(4) == 0x272;
      var s12 := Swap1(s11);
      var s13 := Div(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push20(s15, 0xffffffffffffffffffffffffffffffffffffffff);
      var s17 := And(s16);
      var s18 := Sub(s17);
      var s19 := Push2(s18, 0x07c3);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s20, gas - 1)
      else
        ExecuteFromCFGNode_s27(s20, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 105
    * Starting at 0x749
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x749 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x03);
      assert s1.Peek(2) == 0x272;
      var s2 := Push1(s1, 0x14);
      var s3 := Swap1(s2);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Swap1(s7);
      var s9 := Div(s8);
      var s10 := Push1(s9, 0xff);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x272;
      var s12 := Push1(s11, 0x0a);
      var s13 := Push2(s12, 0x0764);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Push2(s15, 0x122f);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s17, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 275
    * Starting at 0x122f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x764

    requires s0.stack[4] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x764;
      assert s1.Peek(4) == 0x272;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1239);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0e04);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s6, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1239

    requires s0.stack[5] == 0x764

    requires s0.stack[7] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1239;
      assert s1.Peek(5) == 0x764;
      assert s1.Peek(7) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s9, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 276
    * Starting at 0x1239
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1239 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x764

    requires s0.stack[6] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x764;
      assert s1.Peek(6) == 0x272;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1244);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0f20);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s7, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 195
    * Starting at 0xf20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1244

    requires s0.stack[5] == 0x764

    requires s0.stack[7] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1244;
      assert s1.Peek(5) == 0x764;
      assert s1.Peek(7) == 0x272;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s32(s11, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 277
    * Starting at 0x1244
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x764

    requires s0.stack[6] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x764;
      assert s1.Peek(6) == 0x272;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1271);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s6 := Dup5(s5);
      var s7 := Dup5(s6);
      var s8 := Push2(s7, 0x115e);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s9, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 249
    * Starting at 0x115e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x1271

    requires s0.stack[7] == 0x764

    requires s0.stack[9] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1271;
      assert s1.Peek(7) == 0x764;
      assert s1.Peek(9) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x116d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s62(s5, gas - 1)
      else
        ExecuteFromCFGNode_s34(s5, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 250
    * Starting at 0x1165
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1165 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1228);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s5, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 274
    * Starting at 0x1228
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1228 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1271;
      assert s1.Peek(8) == 0x764;
      assert s1.Peek(10) == 0x272;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s7, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 278
    * Starting at 0x1271
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1271 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x764

    requires s0.stack[6] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x764;
      assert s1.Peek(6) == 0x272;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s8, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 106
    * Starting at 0x764
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x764 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x272;
      var s2 := Dup2(s1);
      var s3 := PushN(s2, 7, 0x06499fd9aec040);
      var s4 := Push2(s3, 0x0777);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1279);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s8, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 279
    * Starting at 0x1279
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1279 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x777

    requires s0.stack[5] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x777;
      assert s1.Peek(5) == 0x272;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1283);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0e04);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s6, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1283

    requires s0.stack[5] == 0x777

    requires s0.stack[8] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1283;
      assert s1.Peek(5) == 0x777;
      assert s1.Peek(8) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s9, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 280
    * Starting at 0x1283
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1283 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x777

    requires s0.stack[7] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x777;
      assert s1.Peek(7) == 0x272;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x128e);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e04);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s7, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x128e

    requires s0.stack[5] == 0x777

    requires s0.stack[8] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128e;
      assert s1.Peek(5) == 0x777;
      assert s1.Peek(8) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s9, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 281
    * Starting at 0x128e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x777

    requires s0.stack[7] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x777;
      assert s1.Peek(7) == 0x272;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Mul(s5);
      var s7 := Push2(s6, 0x129c);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0e04);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s10, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x129c

    requires s0.stack[6] == 0x777

    requires s0.stack[9] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x129c;
      assert s1.Peek(6) == 0x777;
      assert s1.Peek(9) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s9, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 282
    * Starting at 0x129c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x777

    requires s0.stack[8] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x777;
      assert s1.Peek(8) == 0x272;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Div(s5);
      var s7 := Dup5(s6);
      var s8 := Eq(s7);
      var s9 := Dup4(s8);
      var s10 := IsZero(s9);
      var s11 := Or(s10);
      assert s11.Peek(5) == 0x777;
      assert s11.Peek(8) == 0x272;
      var s12 := Push2(s11, 0x12b3);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s13, gas - 1)
      else
        ExecuteFromCFGNode_s45(s13, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 283
    * Starting at 0x12ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x777

    requires s0.stack[7] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x12b2);
      assert s1.Peek(0) == 0x12b2;
      assert s1.Peek(5) == 0x777;
      assert s1.Peek(8) == 0x272;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s3, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x12b2

    requires s0.stack[5] == 0x777

    requires s0.stack[8] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12b2;
      assert s1.Peek(5) == 0x777;
      assert s1.Peek(8) == 0x272;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 47
    * Segment Id for this node is: 285
    * Starting at 0x12b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x777

    requires s0.stack[7] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x777;
      assert s1.Peek(7) == 0x272;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s7, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 107
    * Starting at 0x777
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x777 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x272;
      var s2 := Push2(s1, 0x0781);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x1279);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s6, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 279
    * Starting at 0x1279
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1279 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x781

    requires s0.stack[4] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x781;
      assert s1.Peek(4) == 0x272;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1283);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0e04);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s6, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x1283

    requires s0.stack[5] == 0x781

    requires s0.stack[7] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1283;
      assert s1.Peek(5) == 0x781;
      assert s1.Peek(7) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s9, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 280
    * Starting at 0x1283
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1283 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x781

    requires s0.stack[6] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x781;
      assert s1.Peek(6) == 0x272;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x128e);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e04);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s7, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x128e

    requires s0.stack[5] == 0x781

    requires s0.stack[7] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128e;
      assert s1.Peek(5) == 0x781;
      assert s1.Peek(7) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s9, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 281
    * Starting at 0x128e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x781

    requires s0.stack[6] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x781;
      assert s1.Peek(6) == 0x272;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Mul(s5);
      var s7 := Push2(s6, 0x129c);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0e04);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s10, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x129c

    requires s0.stack[6] == 0x781

    requires s0.stack[8] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x129c;
      assert s1.Peek(6) == 0x781;
      assert s1.Peek(8) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s9, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 282
    * Starting at 0x129c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x781

    requires s0.stack[7] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x781;
      assert s1.Peek(7) == 0x272;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Div(s5);
      var s7 := Dup5(s6);
      var s8 := Eq(s7);
      var s9 := Dup4(s8);
      var s10 := IsZero(s9);
      var s11 := Or(s10);
      assert s11.Peek(5) == 0x781;
      assert s11.Peek(7) == 0x272;
      var s12 := Push2(s11, 0x12b3);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s13, gas - 1)
      else
        ExecuteFromCFGNode_s56(s13, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 283
    * Starting at 0x12ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x781

    requires s0.stack[6] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x12b2);
      assert s1.Peek(0) == 0x12b2;
      assert s1.Peek(5) == 0x781;
      assert s1.Peek(7) == 0x272;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s3, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x12b2

    requires s0.stack[5] == 0x781

    requires s0.stack[7] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x12b2;
      assert s1.Peek(5) == 0x781;
      assert s1.Peek(7) == 0x272;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 58
    * Segment Id for this node is: 285
    * Starting at 0x12b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x781

    requires s0.stack[6] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x781;
      assert s1.Peek(6) == 0x272;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s7, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 108
    * Starting at 0x781
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x781 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x272;
      var s2 := Push1(s1, 0x04);
      var s3 := Push0(s2);
      var s4 := Caller(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(5) == 0x272;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push0(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(4) == 0x272;
      var s22 := SStore(s21);
      var s23 := Pop(s22);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s60(s23, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 109
    * Starting at 0x7c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x272;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s3, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 58
    * Starting at 0x272
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x272 as nat
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

  /** Node 62
    * Segment Id for this node is: 251
    * Starting at 0x116d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1271;
      assert s1.Peek(8) == 0x764;
      assert s1.Peek(10) == 0x272;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x117a);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s4, gas - 1)
      else
        ExecuteFromCFGNode_s63(s4, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 252
    * Starting at 0x1173
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1173 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1228);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s5, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 253
    * Starting at 0x117a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1271;
      assert s1.Peek(8) == 0x764;
      assert s1.Peek(10) == 0x272;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x1190);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s7, gas - 1)
      else
        ExecuteFromCFGNode_s65(s7, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 254
    * Starting at 0x1184
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1184 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(6) == 0x1271;
      assert s1.Peek(10) == 0x764;
      assert s1.Peek(12) == 0x272;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x119a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s5, gas - 1)
      else
        ExecuteFromCFGNode_s66(s5, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 255
    * Starting at 0x118c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x11c9);
      assert s1.Peek(0) == 0x11c9;
      assert s1.Peek(6) == 0x1271;
      assert s1.Peek(10) == 0x764;
      assert s1.Peek(12) == 0x272;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s2, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 264
    * Starting at 0x11c9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(7) == 0x1271;
      assert s11.Peek(11) == 0x764;
      assert s11.Peek(13) == 0x272;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x11fe);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s20, gas - 1)
      else
        ExecuteFromCFGNode_s68(s20, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 265
    * Starting at 0x11e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Dup3(s1);
      var s3 := Exp(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Dup4(s5);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x11f9);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s11, gas - 1)
      else
        ExecuteFromCFGNode_s69(s11, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 266
    * Starting at 0x11f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x11f8);
      assert s1.Peek(0) == 0x11f8;
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s3, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x11f8

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x11f8;
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 71
    * Segment Id for this node is: 268
    * Starting at 0x11f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1271;
      assert s1.Peek(8) == 0x764;
      assert s1.Peek(10) == 0x272;
      var s2 := Push2(s1, 0x1228);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s3, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 269
    * Starting at 0x11fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1271;
      assert s1.Peek(8) == 0x764;
      assert s1.Peek(10) == 0x272;
      var s2 := Push2(s1, 0x120b);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push2(s6, 0x110c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s8, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 239
    * Starting at 0x110c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x120b

    requires s0.stack[9] == 0x1271

    requires s0.stack[13] == 0x764

    requires s0.stack[15] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x120b;
      assert s1.Peek(9) == 0x1271;
      assert s1.Peek(13) == 0x764;
      assert s1.Peek(15) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s74(s9, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 240
    * Starting at 0x1115
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1115 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x120b

    requires s0.stack[11] == 0x1271

    requires s0.stack[15] == 0x764

    requires s0.stack[17] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x120b;
      assert s1.Peek(11) == 0x1271;
      assert s1.Peek(15) == 0x764;
      assert s1.Peek(17) == 0x272;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x1155);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s7, gas - 1)
      else
        ExecuteFromCFGNode_s75(s7, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 241
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x120b

    requires s0.stack[11] == 0x1271

    requires s0.stack[15] == 0x764

    requires s0.stack[17] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(7) == 0x120b;
      assert s1.Peek(12) == 0x1271;
      assert s1.Peek(16) == 0x764;
      assert s1.Peek(18) == 0x272;
      var s2 := Dup7(s1);
      var s3 := Div(s2);
      var s4 := Dup2(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x1131);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s8, gas - 1)
      else
        ExecuteFromCFGNode_s76(s8, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 242
    * Starting at 0x1129
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1129 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x120b

    requires s0.stack[11] == 0x1271

    requires s0.stack[15] == 0x764

    requires s0.stack[17] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1130);
      assert s1.Peek(0) == 0x1130;
      assert s1.Peek(7) == 0x120b;
      assert s1.Peek(12) == 0x1271;
      assert s1.Peek(16) == 0x764;
      assert s1.Peek(18) == 0x272;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s3, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x1130

    requires s0.stack[7] == 0x120b

    requires s0.stack[12] == 0x1271

    requires s0.stack[16] == 0x764

    requires s0.stack[18] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1130;
      assert s1.Peek(7) == 0x120b;
      assert s1.Peek(12) == 0x1271;
      assert s1.Peek(16) == 0x764;
      assert s1.Peek(18) == 0x272;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 78
    * Segment Id for this node is: 244
    * Starting at 0x1131
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1131 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x120b

    requires s0.stack[11] == 0x1271

    requires s0.stack[15] == 0x764

    requires s0.stack[17] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x120b;
      assert s1.Peek(11) == 0x1271;
      assert s1.Peek(15) == 0x764;
      assert s1.Peek(17) == 0x272;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x1140);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s80(s7, gas - 1)
      else
        ExecuteFromCFGNode_s79(s7, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 245
    * Starting at 0x113b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x120b

    requires s0.stack[11] == 0x1271

    requires s0.stack[15] == 0x764

    requires s0.stack[17] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(7) == 0x120b;
      assert s1.Peek(12) == 0x1271;
      assert s1.Peek(16) == 0x764;
      assert s1.Peek(18) == 0x272;
      var s2 := Dup3(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s80(s5, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 246
    * Starting at 0x1140
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1140 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x120b

    requires s0.stack[11] == 0x1271

    requires s0.stack[15] == 0x764

    requires s0.stack[17] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x120b;
      assert s1.Peek(11) == 0x1271;
      assert s1.Peek(15) == 0x764;
      assert s1.Peek(17) == 0x272;
      var s2 := Dup1(s1);
      var s3 := Dup2(s2);
      var s4 := Mul(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x114e);
      var s8 := Dup6(s7);
      var s9 := Push2(s8, 0x1100);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s10, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 238
    * Starting at 0x1100
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1100 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x114e

    requires s0.stack[8] == 0x120b

    requires s0.stack[13] == 0x1271

    requires s0.stack[17] == 0x764

    requires s0.stack[19] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x114e;
      assert s1.Peek(8) == 0x120b;
      assert s1.Peek(13) == 0x1271;
      assert s1.Peek(17) == 0x764;
      assert s1.Peek(19) == 0x272;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s11, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 247
    * Starting at 0x114e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x120b

    requires s0.stack[12] == 0x1271

    requires s0.stack[16] == 0x764

    requires s0.stack[18] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x120b;
      assert s1.Peek(12) == 0x1271;
      assert s1.Peek(16) == 0x764;
      assert s1.Peek(18) == 0x272;
      var s2 := Swap5(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1115);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s5, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 248
    * Starting at 0x1155
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1155 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x120b

    requires s0.stack[11] == 0x1271

    requires s0.stack[15] == 0x764

    requires s0.stack[17] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x120b;
      assert s1.Peek(11) == 0x1271;
      assert s1.Peek(15) == 0x764;
      assert s1.Peek(17) == 0x272;
      var s2 := Swap5(s1);
      var s3 := Pop(s2);
      var s4 := Swap5(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s9, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 270
    * Starting at 0x120b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x1271

    requires s0.stack[10] == 0x764

    requires s0.stack[12] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1271;
      assert s1.Peek(10) == 0x764;
      assert s1.Peek(12) == 0x272;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Div(s7);
      var s9 := Dup2(s8);
      var s10 := Gt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(5) == 0x1271;
      assert s11.Peek(9) == 0x764;
      assert s11.Peek(11) == 0x272;
      var s12 := Push2(s11, 0x1222);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s13, gas - 1)
      else
        ExecuteFromCFGNode_s85(s13, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 271
    * Starting at 0x121a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1221);
      assert s1.Peek(0) == 0x1221;
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s3, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x1221

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1221;
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 87
    * Segment Id for this node is: 273
    * Starting at 0x1222
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x1271

    requires s0.stack[8] == 0x764

    requires s0.stack[10] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1271;
      assert s1.Peek(8) == 0x764;
      assert s1.Peek(10) == 0x272;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Mul(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s35(s6, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 257
    * Starting at 0x119a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x119a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x11ac);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s91(s7, gas - 1)
      else
        ExecuteFromCFGNode_s89(s7, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 258
    * Starting at 0x11a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x11ab);
      assert s1.Peek(0) == 0x11ab;
      assert s1.Peek(6) == 0x1271;
      assert s1.Peek(10) == 0x764;
      assert s1.Peek(12) == 0x272;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s3, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x11ab

    requires s0.stack[6] == 0x1271

    requires s0.stack[10] == 0x764

    requires s0.stack[12] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x11ab;
      assert s1.Peek(6) == 0x1271;
      assert s1.Peek(10) == 0x764;
      assert s1.Peek(12) == 0x272;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 91
    * Segment Id for this node is: 260
    * Starting at 0x11ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Exp(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup5(s6);
      var s8 := Dup3(s7);
      var s9 := Gt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x11c3);
      assert s11.Peek(0) == 0x11c3;
      assert s11.Peek(7) == 0x1271;
      assert s11.Peek(11) == 0x764;
      assert s11.Peek(13) == 0x272;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s12, gas - 1)
      else
        ExecuteFromCFGNode_s92(s12, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 261
    * Starting at 0x11bb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x11c2);
      assert s1.Peek(0) == 0x11c2;
      assert s1.Peek(6) == 0x1271;
      assert s1.Peek(10) == 0x764;
      assert s1.Peek(12) == 0x272;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s3, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x11c2

    requires s0.stack[6] == 0x1271

    requires s0.stack[10] == 0x764

    requires s0.stack[12] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x11c2;
      assert s1.Peek(6) == 0x1271;
      assert s1.Peek(10) == 0x764;
      assert s1.Peek(12) == 0x272;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 94
    * Segment Id for this node is: 263
    * Starting at 0x11c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x1228);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s4, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 256
    * Starting at 0x1190
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1190 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1271

    requires s0.stack[9] == 0x764

    requires s0.stack[11] == 0x272

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1271;
      assert s1.Peek(9) == 0x764;
      assert s1.Peek(11) == 0x272;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x1228);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s7, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 52
    * Starting at 0x228
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x228 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0242);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x023d);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x23d;
      assert s11.Peek(3) == 0x242;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0fa7);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s14, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 209
    * Starting at 0xfa7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x23d

    requires s0.stack[3] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x23d;
      assert s1.Peek(3) == 0x242;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0fbd);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s11, gas - 1)
      else
        ExecuteFromCFGNode_s98(s11, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 210
    * Starting at 0xfb5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x23d

    requires s0.stack[5] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0fbc);
      assert s1.Peek(0) == 0xfbc;
      assert s1.Peek(5) == 0x23d;
      assert s1.Peek(6) == 0x242;
      var s2 := Push2(s1, 0x0da6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s3, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 156
    * Starting at 0xda6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xfbc

    requires s0.stack[5] == 0x23d

    requires s0.stack[6] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xfbc;
      assert s1.Peek(5) == 0x23d;
      assert s1.Peek(6) == 0x242;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 100
    * Segment Id for this node is: 212
    * Starting at 0xfbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x23d

    requires s0.stack[5] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x23d;
      assert s1.Peek(5) == 0x242;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0fca);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0df0);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s9, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 164
    * Starting at 0xdf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xfca

    requires s0.stack[8] == 0x23d

    requires s0.stack[9] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfca;
      assert s1.Peek(8) == 0x23d;
      assert s1.Peek(9) == 0x242;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0dfe);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s10, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 160
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xfca

    requires s0.stack[11] == 0x23d

    requires s0.stack[12] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xfca;
      assert s1.Peek(11) == 0x23d;
      assert s1.Peek(12) == 0x242;
      var s2 := Push2(s1, 0x0de3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s5, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xde3

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0xfca

    requires s0.stack[13] == 0x23d

    requires s0.stack[14] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde3;
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0xfca;
      assert s1.Peek(13) == 0x23d;
      assert s1.Peek(14) == 0x242;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s6, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xde3

    requires s0.stack[6] == 0xdfe

    requires s0.stack[10] == 0xfca

    requires s0.stack[16] == 0x23d

    requires s0.stack[17] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(6) == 0xdfe;
      assert s1.Peek(10) == 0xfca;
      assert s1.Peek(16) == 0x23d;
      assert s1.Peek(17) == 0x242;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s105(s11, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xde3

    requires s0.stack[5] == 0xdfe

    requires s0.stack[9] == 0xfca

    requires s0.stack[15] == 0x23d

    requires s0.stack[16] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(5) == 0xdfe;
      assert s1.Peek(9) == 0xfca;
      assert s1.Peek(15) == 0x23d;
      assert s1.Peek(16) == 0x242;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s7, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 161
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0xfca

    requires s0.stack[12] == 0x23d

    requires s0.stack[13] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xfca;
      assert s1.Peek(12) == 0x23d;
      assert s1.Peek(13) == 0x242;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ded);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s5, gas - 1)
      else
        ExecuteFromCFGNode_s107(s5, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 162
    * Starting at 0xdea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xfca

    requires s0.stack[11] == 0x23d

    requires s0.stack[12] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xfca;
      assert s1.Peek(12) == 0x23d;
      assert s1.Peek(13) == 0x242;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 108
    * Segment Id for this node is: 163
    * Starting at 0xded
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xfca

    requires s0.stack[11] == 0x23d

    requires s0.stack[12] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xfca;
      assert s1.Peek(11) == 0x23d;
      assert s1.Peek(12) == 0x242;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s3, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 165
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xfca

    requires s0.stack[9] == 0x23d

    requires s0.stack[10] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfca;
      assert s1.Peek(9) == 0x23d;
      assert s1.Peek(10) == 0x242;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s6, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 213
    * Starting at 0xfca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x23d

    requires s0.stack[7] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x23d;
      assert s1.Peek(7) == 0x242;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0fdb);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0df0);
      assert s11.Peek(0) == 0xdf0;
      assert s11.Peek(3) == 0xfdb;
      assert s11.Peek(9) == 0x23d;
      assert s11.Peek(10) == 0x242;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s12, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 164
    * Starting at 0xdf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xfdb

    requires s0.stack[8] == 0x23d

    requires s0.stack[9] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfdb;
      assert s1.Peek(8) == 0x23d;
      assert s1.Peek(9) == 0x242;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0dfe);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s10, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 160
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xfdb

    requires s0.stack[11] == 0x23d

    requires s0.stack[12] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xfdb;
      assert s1.Peek(11) == 0x23d;
      assert s1.Peek(12) == 0x242;
      var s2 := Push2(s1, 0x0de3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s5, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xde3

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0xfdb

    requires s0.stack[13] == 0x23d

    requires s0.stack[14] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde3;
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0xfdb;
      assert s1.Peek(13) == 0x23d;
      assert s1.Peek(14) == 0x242;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s6, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xde3

    requires s0.stack[6] == 0xdfe

    requires s0.stack[10] == 0xfdb

    requires s0.stack[16] == 0x23d

    requires s0.stack[17] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(6) == 0xdfe;
      assert s1.Peek(10) == 0xfdb;
      assert s1.Peek(16) == 0x23d;
      assert s1.Peek(17) == 0x242;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s115(s11, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xde3

    requires s0.stack[5] == 0xdfe

    requires s0.stack[9] == 0xfdb

    requires s0.stack[15] == 0x23d

    requires s0.stack[16] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(5) == 0xdfe;
      assert s1.Peek(9) == 0xfdb;
      assert s1.Peek(15) == 0x23d;
      assert s1.Peek(16) == 0x242;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s7, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 161
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0xfdb

    requires s0.stack[12] == 0x23d

    requires s0.stack[13] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xfdb;
      assert s1.Peek(12) == 0x23d;
      assert s1.Peek(13) == 0x242;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ded);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s5, gas - 1)
      else
        ExecuteFromCFGNode_s117(s5, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 162
    * Starting at 0xdea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xfdb

    requires s0.stack[11] == 0x23d

    requires s0.stack[12] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xfdb;
      assert s1.Peek(12) == 0x23d;
      assert s1.Peek(13) == 0x242;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 118
    * Segment Id for this node is: 163
    * Starting at 0xded
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xfdb

    requires s0.stack[11] == 0x23d

    requires s0.stack[12] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xfdb;
      assert s1.Peek(11) == 0x23d;
      assert s1.Peek(12) == 0x242;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s3, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 165
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xfdb

    requires s0.stack[9] == 0x23d

    requires s0.stack[10] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfdb;
      assert s1.Peek(9) == 0x23d;
      assert s1.Peek(10) == 0x242;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s6, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 214
    * Starting at 0xfdb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x23d

    requires s0.stack[7] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x23d;
      assert s1.Peek(7) == 0x242;
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
      ExecuteFromCFGNode_s121(s10, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 53
    * Starting at 0x23d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x242;
      var s2 := Push2(s1, 0x0672);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s3, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 102
    * Starting at 0x672
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x672 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x242;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x242;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(5) == 0x242;
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
      assert s31.Peek(5) == 0x242;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s123(s41, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 103
    * Starting at 0x6f0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x242

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x242;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s4, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 54
    * Starting at 0x242
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x242 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x024f);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0eb7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s8, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 186
    * Starting at 0xeb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24f;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0eca);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xeca;
      assert s11.Peek(5) == 0x24f;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0ea8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s14, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 184
    * Starting at 0xea8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xeca

    requires s0.stack[6] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeca;
      assert s1.Peek(6) == 0x24f;
      var s2 := Push2(s1, 0x0eb1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s5, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xeb1

    requires s0.stack[4] == 0xeca

    requires s0.stack[8] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb1;
      assert s1.Peek(4) == 0xeca;
      assert s1.Peek(8) == 0x24f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s9, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 185
    * Starting at 0xeb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xeca

    requires s0.stack[7] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xeca;
      assert s1.Peek(7) == 0x24f;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s6, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 187
    * Starting at 0xeca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x24f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x24f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s6, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 55
    * Starting at 0x24f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24f as nat
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

  /** Node 131
    * Segment Id for this node is: 49
    * Starting at 0x20a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0212);
      var s3 := Push2(s2, 0x05ca);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s4, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 97
    * Starting at 0x5ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x212;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0x5c69bee701ef814a2b6a3edd4b1652cb9cc5aa6f);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Push4(s5, 0xe6a43905);
      var s7 := Push20(s6, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2);
      var s8 := Address(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x212;
      var s12 := Push4(s11, 0xffffffff);
      var s13 := And(s12);
      var s14 := Push1(s13, 0xe0);
      var s15 := Shl(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x04);
      var s19 := Add(s18);
      var s20 := Push2(s19, 0x062e);
      var s21 := Swap3(s20);
      assert s21.Peek(3) == 0x62e;
      assert s21.Peek(7) == 0x212;
      var s22 := Swap2(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x106d);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s25, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 227
    * Starting at 0x106d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x62e

    requires s0.stack[7] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x62e;
      assert s1.Peek(7) == 0x212;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1080);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1080;
      assert s11.Peek(6) == 0x62e;
      assert s11.Peek(10) == 0x212;
      var s12 := Dup6(s11);
      var s13 := Push2(s12, 0x0f7f);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s14, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 205
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x1080

    requires s0.stack[7] == 0x62e

    requires s0.stack[11] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1080;
      assert s1.Peek(7) == 0x62e;
      assert s1.Peek(11) == 0x212;
      var s2 := Push2(s1, 0x0f88);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s5, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xf88

    requires s0.stack[4] == 0x1080

    requires s0.stack[9] == 0x62e

    requires s0.stack[13] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf88;
      assert s1.Peek(4) == 0x1080;
      assert s1.Peek(9) == 0x62e;
      assert s1.Peek(13) == 0x212;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s6, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xf88

    requires s0.stack[7] == 0x1080

    requires s0.stack[12] == 0x62e

    requires s0.stack[16] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xf88;
      assert s1.Peek(7) == 0x1080;
      assert s1.Peek(12) == 0x62e;
      assert s1.Peek(16) == 0x212;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s137(s11, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xf88

    requires s0.stack[6] == 0x1080

    requires s0.stack[11] == 0x62e

    requires s0.stack[15] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf88;
      assert s1.Peek(6) == 0x1080;
      assert s1.Peek(11) == 0x62e;
      assert s1.Peek(15) == 0x212;
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
    * Segment Id for this node is: 206
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x1080

    requires s0.stack[8] == 0x62e

    requires s0.stack[12] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1080;
      assert s1.Peek(8) == 0x62e;
      assert s1.Peek(12) == 0x212;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s6, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 228
    * Starting at 0x1080
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1080 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x62e

    requires s0.stack[8] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x62e;
      assert s1.Peek(8) == 0x212;
      var s2 := Push2(s1, 0x108d);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0f7f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s8, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 205
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x108d

    requires s0.stack[7] == 0x62e

    requires s0.stack[11] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x108d;
      assert s1.Peek(7) == 0x62e;
      assert s1.Peek(11) == 0x212;
      var s2 := Push2(s1, 0x0f88);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s5, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xf88

    requires s0.stack[4] == 0x108d

    requires s0.stack[9] == 0x62e

    requires s0.stack[13] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf88;
      assert s1.Peek(4) == 0x108d;
      assert s1.Peek(9) == 0x62e;
      assert s1.Peek(13) == 0x212;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s6, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xf88

    requires s0.stack[7] == 0x108d

    requires s0.stack[12] == 0x62e

    requires s0.stack[16] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xf88;
      assert s1.Peek(7) == 0x108d;
      assert s1.Peek(12) == 0x62e;
      assert s1.Peek(16) == 0x212;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s143(s11, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xf88

    requires s0.stack[6] == 0x108d

    requires s0.stack[11] == 0x62e

    requires s0.stack[15] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf88;
      assert s1.Peek(6) == 0x108d;
      assert s1.Peek(11) == 0x62e;
      assert s1.Peek(15) == 0x212;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s7, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 206
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x108d

    requires s0.stack[8] == 0x62e

    requires s0.stack[12] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x108d;
      assert s1.Peek(8) == 0x62e;
      assert s1.Peek(12) == 0x212;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s6, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 229
    * Starting at 0x108d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x62e

    requires s0.stack[8] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x62e;
      assert s1.Peek(8) == 0x212;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s7, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 98
    * Starting at 0x62e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x212;
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(5) == 0x212;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0649);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s16, gas - 1)
      else
        ExecuteFromCFGNode_s147(s16, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 99
    * Starting at 0x642
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x642 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(6) == 0x212;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 148
    * Segment Id for this node is: 100
    * Starting at 0x649
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x649 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x212;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Not(s9);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(5) == 0x212;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := And(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Dup1(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(4) == 0x212;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x066d);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x10a8);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s28, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 232
    * Starting at 0x10a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x66d

    requires s0.stack[4] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x66d;
      assert s1.Peek(4) == 0x212;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x10bd);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s10, gas - 1)
      else
        ExecuteFromCFGNode_s150(s10, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 233
    * Starting at 0x10b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x66d

    requires s0.stack[5] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x10bc);
      assert s1.Peek(0) == 0x10bc;
      assert s1.Peek(4) == 0x66d;
      assert s1.Peek(6) == 0x212;
      var s2 := Push2(s1, 0x0da6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s3, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 156
    * Starting at 0xda6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x10bc

    requires s0.stack[4] == 0x66d

    requires s0.stack[6] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10bc;
      assert s1.Peek(4) == 0x66d;
      assert s1.Peek(6) == 0x212;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 152
    * Segment Id for this node is: 235
    * Starting at 0x10bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x66d

    requires s0.stack[5] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x66d;
      assert s1.Peek(5) == 0x212;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x10ca);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x1094);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s9, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 230
    * Starting at 0x1094
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x10ca

    requires s0.stack[7] == 0x66d

    requires s0.stack[9] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ca;
      assert s1.Peek(7) == 0x66d;
      assert s1.Peek(9) == 0x212;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x10a2);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s10, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 160
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x10a2

    requires s0.stack[5] == 0x10ca

    requires s0.stack[10] == 0x66d

    requires s0.stack[12] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10a2;
      assert s1.Peek(5) == 0x10ca;
      assert s1.Peek(10) == 0x66d;
      assert s1.Peek(12) == 0x212;
      var s2 := Push2(s1, 0x0de3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s5, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xde3

    requires s0.stack[3] == 0x10a2

    requires s0.stack[7] == 0x10ca

    requires s0.stack[12] == 0x66d

    requires s0.stack[14] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde3;
      assert s1.Peek(3) == 0x10a2;
      assert s1.Peek(7) == 0x10ca;
      assert s1.Peek(12) == 0x66d;
      assert s1.Peek(14) == 0x212;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s6, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xde3

    requires s0.stack[6] == 0x10a2

    requires s0.stack[10] == 0x10ca

    requires s0.stack[15] == 0x66d

    requires s0.stack[17] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(6) == 0x10a2;
      assert s1.Peek(10) == 0x10ca;
      assert s1.Peek(15) == 0x66d;
      assert s1.Peek(17) == 0x212;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s157(s11, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xde3

    requires s0.stack[5] == 0x10a2

    requires s0.stack[9] == 0x10ca

    requires s0.stack[14] == 0x66d

    requires s0.stack[16] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(5) == 0x10a2;
      assert s1.Peek(9) == 0x10ca;
      assert s1.Peek(14) == 0x66d;
      assert s1.Peek(16) == 0x212;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s7, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 161
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x10a2

    requires s0.stack[6] == 0x10ca

    requires s0.stack[11] == 0x66d

    requires s0.stack[13] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10a2;
      assert s1.Peek(6) == 0x10ca;
      assert s1.Peek(11) == 0x66d;
      assert s1.Peek(13) == 0x212;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ded);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s160(s5, gas - 1)
      else
        ExecuteFromCFGNode_s159(s5, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 162
    * Starting at 0xdea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x10a2

    requires s0.stack[5] == 0x10ca

    requires s0.stack[10] == 0x66d

    requires s0.stack[12] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0x10a2;
      assert s1.Peek(6) == 0x10ca;
      assert s1.Peek(11) == 0x66d;
      assert s1.Peek(13) == 0x212;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 160
    * Segment Id for this node is: 163
    * Starting at 0xded
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x10a2

    requires s0.stack[5] == 0x10ca

    requires s0.stack[10] == 0x66d

    requires s0.stack[12] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10a2;
      assert s1.Peek(5) == 0x10ca;
      assert s1.Peek(10) == 0x66d;
      assert s1.Peek(12) == 0x212;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s3, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 231
    * Starting at 0x10a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x10ca

    requires s0.stack[8] == 0x66d

    requires s0.stack[10] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10ca;
      assert s1.Peek(8) == 0x66d;
      assert s1.Peek(10) == 0x212;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s6, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 236
    * Starting at 0x10ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x66d

    requires s0.stack[7] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x66d;
      assert s1.Peek(7) == 0x212;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s9, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 101
    * Starting at 0x66d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x212;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s5, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 50
    * Starting at 0x212
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x212 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x021f);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0f8e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s8, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 207
    * Starting at 0xf8e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x21f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x21f;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0fa1);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xfa1;
      assert s11.Peek(5) == 0x21f;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0f7f);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s14, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 205
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xfa1

    requires s0.stack[6] == 0x21f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfa1;
      assert s1.Peek(6) == 0x21f;
      var s2 := Push2(s1, 0x0f88);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s5, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf88

    requires s0.stack[4] == 0xfa1

    requires s0.stack[8] == 0x21f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf88;
      assert s1.Peek(4) == 0xfa1;
      assert s1.Peek(8) == 0x21f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s6, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xf88

    requires s0.stack[7] == 0xfa1

    requires s0.stack[11] == 0x21f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xf88;
      assert s1.Peek(7) == 0xfa1;
      assert s1.Peek(11) == 0x21f;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s169(s11, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf88

    requires s0.stack[6] == 0xfa1

    requires s0.stack[10] == 0x21f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf88;
      assert s1.Peek(6) == 0xfa1;
      assert s1.Peek(10) == 0x21f;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s7, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 206
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xfa1

    requires s0.stack[7] == 0x21f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfa1;
      assert s1.Peek(7) == 0x21f;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s6, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 208
    * Starting at 0xfa1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x21f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x21f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s6, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 51
    * Starting at 0x21f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21f as nat
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

  /** Node 173
    * Segment Id for this node is: 46
    * Starting at 0x1ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0208);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0203);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x203;
      assert s11.Peek(3) == 0x208;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f54);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s14, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 200
    * Starting at 0xf54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x203

    requires s0.stack[3] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x203;
      assert s1.Peek(3) == 0x208;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0f69);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s10, gas - 1)
      else
        ExecuteFromCFGNode_s175(s10, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 201
    * Starting at 0xf61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x203

    requires s0.stack[4] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f68);
      assert s1.Peek(0) == 0xf68;
      assert s1.Peek(4) == 0x203;
      assert s1.Peek(5) == 0x208;
      var s2 := Push2(s1, 0x0da6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s3, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 156
    * Starting at 0xda6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0xf68

    requires s0.stack[4] == 0x203

    requires s0.stack[5] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf68;
      assert s1.Peek(4) == 0x203;
      assert s1.Peek(5) == 0x208;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 177
    * Segment Id for this node is: 203
    * Starting at 0xf69
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x203

    requires s0.stack[4] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x203;
      assert s1.Peek(4) == 0x208;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f76);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0df0);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s9, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 164
    * Starting at 0xdf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xf76

    requires s0.stack[7] == 0x203

    requires s0.stack[8] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf76;
      assert s1.Peek(7) == 0x203;
      assert s1.Peek(8) == 0x208;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0dfe);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s10, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 160
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xf76

    requires s0.stack[10] == 0x203

    requires s0.stack[11] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xf76;
      assert s1.Peek(10) == 0x203;
      assert s1.Peek(11) == 0x208;
      var s2 := Push2(s1, 0x0de3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s5, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xde3

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0xf76

    requires s0.stack[12] == 0x203

    requires s0.stack[13] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde3;
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0xf76;
      assert s1.Peek(12) == 0x203;
      assert s1.Peek(13) == 0x208;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s6, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xde3

    requires s0.stack[6] == 0xdfe

    requires s0.stack[10] == 0xf76

    requires s0.stack[15] == 0x203

    requires s0.stack[16] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(6) == 0xdfe;
      assert s1.Peek(10) == 0xf76;
      assert s1.Peek(15) == 0x203;
      assert s1.Peek(16) == 0x208;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s182(s11, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xde3

    requires s0.stack[5] == 0xdfe

    requires s0.stack[9] == 0xf76

    requires s0.stack[14] == 0x203

    requires s0.stack[15] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(5) == 0xdfe;
      assert s1.Peek(9) == 0xf76;
      assert s1.Peek(14) == 0x203;
      assert s1.Peek(15) == 0x208;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s7, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 161
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0xf76

    requires s0.stack[11] == 0x203

    requires s0.stack[12] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xf76;
      assert s1.Peek(11) == 0x203;
      assert s1.Peek(12) == 0x208;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ded);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s185(s5, gas - 1)
      else
        ExecuteFromCFGNode_s184(s5, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 162
    * Starting at 0xdea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xf76

    requires s0.stack[10] == 0x203

    requires s0.stack[11] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xf76;
      assert s1.Peek(11) == 0x203;
      assert s1.Peek(12) == 0x208;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 185
    * Segment Id for this node is: 163
    * Starting at 0xded
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xf76

    requires s0.stack[10] == 0x203

    requires s0.stack[11] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xf76;
      assert s1.Peek(10) == 0x203;
      assert s1.Peek(11) == 0x208;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s3, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 165
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xf76

    requires s0.stack[8] == 0x203

    requires s0.stack[9] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf76;
      assert s1.Peek(8) == 0x203;
      assert s1.Peek(9) == 0x208;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s6, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 204
    * Starting at 0xf76
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf76 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x203

    requires s0.stack[6] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x203;
      assert s1.Peek(6) == 0x208;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s9, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 47
    * Starting at 0x203
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x208;
      var s2 := Push2(s1, 0x044b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s3, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 87
    * Starting at 0x44b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x208;
      var s2 := Caller(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Push1(s4, 0x03);
      var s6 := Push0(s5);
      var s7 := Swap1(s6);
      var s8 := SLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0100);
      var s11 := Exp(s10);
      assert s11.Peek(4) == 0x208;
      var s12 := Swap1(s11);
      var s13 := Div(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push20(s15, 0xffffffffffffffffffffffffffffffffffffffff);
      var s17 := And(s16);
      var s18 := Eq(s17);
      var s19 := Dup1(s18);
      var s20 := IsZero(s19);
      var s21 := Push2(s20, 0x04f4);
      assert s21.Peek(0) == 0x4f4;
      assert s21.Peek(4) == 0x208;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s22, gas - 1)
      else
        ExecuteFromCFGNode_s190(s22, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 88
    * Starting at 0x4a2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0x208;
      var s2 := Dup1(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Push1(s4, 0x03);
      var s6 := Push0(s5);
      var s7 := Swap1(s6);
      var s8 := SLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0100);
      var s11 := Exp(s10);
      assert s11.Peek(4) == 0x208;
      var s12 := Swap1(s11);
      var s13 := Div(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push20(s15, 0xffffffffffffffffffffffffffffffffffffffff);
      var s17 := And(s16);
      var s18 := Eq(s17);
      var s19 := IsZero(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s191(s19, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 89
    * Starting at 0x4f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x208;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0533);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s226(s5, gas - 1)
      else
        ExecuteFromCFGNode_s192(s5, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 90
    * Starting at 0x4fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0x208;
      var s2 := Dup1(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x051a);
      var s6 := Push2(s5, 0x05ca);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s7, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 97
    * Starting at 0x5ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x51a

    requires s0.stack[3] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x51a;
      assert s1.Peek(3) == 0x208;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0x5c69bee701ef814a2b6a3edd4b1652cb9cc5aa6f);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Push4(s5, 0xe6a43905);
      var s7 := Push20(s6, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2);
      var s8 := Address(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x51a;
      assert s11.Peek(10) == 0x208;
      var s12 := Push4(s11, 0xffffffff);
      var s13 := And(s12);
      var s14 := Push1(s13, 0xe0);
      var s15 := Shl(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x04);
      var s19 := Add(s18);
      var s20 := Push2(s19, 0x062e);
      var s21 := Swap3(s20);
      assert s21.Peek(3) == 0x62e;
      assert s21.Peek(7) == 0x51a;
      assert s21.Peek(10) == 0x208;
      var s22 := Swap2(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x106d);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s25, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 227
    * Starting at 0x106d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x62e

    requires s0.stack[7] == 0x51a

    requires s0.stack[10] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x62e;
      assert s1.Peek(7) == 0x51a;
      assert s1.Peek(10) == 0x208;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x1080);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x1080;
      assert s11.Peek(6) == 0x62e;
      assert s11.Peek(10) == 0x51a;
      assert s11.Peek(13) == 0x208;
      var s12 := Dup6(s11);
      var s13 := Push2(s12, 0x0f7f);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s14, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 205
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x1080

    requires s0.stack[7] == 0x62e

    requires s0.stack[11] == 0x51a

    requires s0.stack[14] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1080;
      assert s1.Peek(7) == 0x62e;
      assert s1.Peek(11) == 0x51a;
      assert s1.Peek(14) == 0x208;
      var s2 := Push2(s1, 0x0f88);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s5, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xf88

    requires s0.stack[4] == 0x1080

    requires s0.stack[9] == 0x62e

    requires s0.stack[13] == 0x51a

    requires s0.stack[16] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf88;
      assert s1.Peek(4) == 0x1080;
      assert s1.Peek(9) == 0x62e;
      assert s1.Peek(13) == 0x51a;
      assert s1.Peek(16) == 0x208;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s6, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xf88

    requires s0.stack[7] == 0x1080

    requires s0.stack[12] == 0x62e

    requires s0.stack[16] == 0x51a

    requires s0.stack[19] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xf88;
      assert s1.Peek(7) == 0x1080;
      assert s1.Peek(12) == 0x62e;
      assert s1.Peek(16) == 0x51a;
      assert s1.Peek(19) == 0x208;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s198(s11, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xf88

    requires s0.stack[6] == 0x1080

    requires s0.stack[11] == 0x62e

    requires s0.stack[15] == 0x51a

    requires s0.stack[18] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf88;
      assert s1.Peek(6) == 0x1080;
      assert s1.Peek(11) == 0x62e;
      assert s1.Peek(15) == 0x51a;
      assert s1.Peek(18) == 0x208;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s7, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 206
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1080

    requires s0.stack[8] == 0x62e

    requires s0.stack[12] == 0x51a

    requires s0.stack[15] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1080;
      assert s1.Peek(8) == 0x62e;
      assert s1.Peek(12) == 0x51a;
      assert s1.Peek(15) == 0x208;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s6, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 228
    * Starting at 0x1080
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1080 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x62e

    requires s0.stack[8] == 0x51a

    requires s0.stack[11] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x62e;
      assert s1.Peek(8) == 0x51a;
      assert s1.Peek(11) == 0x208;
      var s2 := Push2(s1, 0x108d);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0f7f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s8, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 205
    * Starting at 0xf7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x108d

    requires s0.stack[7] == 0x62e

    requires s0.stack[11] == 0x51a

    requires s0.stack[14] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x108d;
      assert s1.Peek(7) == 0x62e;
      assert s1.Peek(11) == 0x51a;
      assert s1.Peek(14) == 0x208;
      var s2 := Push2(s1, 0x0f88);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s5, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xf88

    requires s0.stack[4] == 0x108d

    requires s0.stack[9] == 0x62e

    requires s0.stack[13] == 0x51a

    requires s0.stack[16] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf88;
      assert s1.Peek(4) == 0x108d;
      assert s1.Peek(9) == 0x62e;
      assert s1.Peek(13) == 0x51a;
      assert s1.Peek(16) == 0x208;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s6, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xf88

    requires s0.stack[7] == 0x108d

    requires s0.stack[12] == 0x62e

    requires s0.stack[16] == 0x51a

    requires s0.stack[19] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xf88;
      assert s1.Peek(7) == 0x108d;
      assert s1.Peek(12) == 0x62e;
      assert s1.Peek(16) == 0x51a;
      assert s1.Peek(19) == 0x208;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s204(s11, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xf88

    requires s0.stack[6] == 0x108d

    requires s0.stack[11] == 0x62e

    requires s0.stack[15] == 0x51a

    requires s0.stack[18] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf88;
      assert s1.Peek(6) == 0x108d;
      assert s1.Peek(11) == 0x62e;
      assert s1.Peek(15) == 0x51a;
      assert s1.Peek(18) == 0x208;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s7, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 206
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x108d

    requires s0.stack[8] == 0x62e

    requires s0.stack[12] == 0x51a

    requires s0.stack[15] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x108d;
      assert s1.Peek(8) == 0x62e;
      assert s1.Peek(12) == 0x51a;
      assert s1.Peek(15) == 0x208;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s6, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 229
    * Starting at 0x108d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x62e

    requires s0.stack[8] == 0x51a

    requires s0.stack[11] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x62e;
      assert s1.Peek(8) == 0x51a;
      assert s1.Peek(11) == 0x208;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s7, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 98
    * Starting at 0x62e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x51a

    requires s0.stack[7] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x51a;
      assert s1.Peek(7) == 0x208;
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(5) == 0x51a;
      assert s11.Peek(8) == 0x208;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0649);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s209(s16, gas - 1)
      else
        ExecuteFromCFGNode_s208(s16, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 99
    * Starting at 0x642
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x642 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x51a

    requires s0.stack[8] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(6) == 0x51a;
      assert s1.Peek(9) == 0x208;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 209
    * Segment Id for this node is: 100
    * Starting at 0x649
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x649 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x51a

    requires s0.stack[8] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x51a;
      assert s1.Peek(8) == 0x208;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Not(s9);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(5) == 0x51a;
      assert s11.Peek(8) == 0x208;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := And(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Dup1(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(4) == 0x51a;
      assert s21.Peek(7) == 0x208;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x066d);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x10a8);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s28, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 232
    * Starting at 0x10a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x66d

    requires s0.stack[4] == 0x51a

    requires s0.stack[7] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x66d;
      assert s1.Peek(4) == 0x51a;
      assert s1.Peek(7) == 0x208;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x10bd);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s213(s10, gas - 1)
      else
        ExecuteFromCFGNode_s211(s10, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 233
    * Starting at 0x10b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x66d

    requires s0.stack[5] == 0x51a

    requires s0.stack[8] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x10bc);
      assert s1.Peek(0) == 0x10bc;
      assert s1.Peek(4) == 0x66d;
      assert s1.Peek(6) == 0x51a;
      assert s1.Peek(9) == 0x208;
      var s2 := Push2(s1, 0x0da6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s3, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 156
    * Starting at 0xda6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x10bc

    requires s0.stack[4] == 0x66d

    requires s0.stack[6] == 0x51a

    requires s0.stack[9] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10bc;
      assert s1.Peek(4) == 0x66d;
      assert s1.Peek(6) == 0x51a;
      assert s1.Peek(9) == 0x208;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 213
    * Segment Id for this node is: 235
    * Starting at 0x10bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x66d

    requires s0.stack[5] == 0x51a

    requires s0.stack[8] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x66d;
      assert s1.Peek(5) == 0x51a;
      assert s1.Peek(8) == 0x208;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x10ca);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x1094);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s9, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 230
    * Starting at 0x1094
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x10ca

    requires s0.stack[7] == 0x66d

    requires s0.stack[9] == 0x51a

    requires s0.stack[12] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ca;
      assert s1.Peek(7) == 0x66d;
      assert s1.Peek(9) == 0x51a;
      assert s1.Peek(12) == 0x208;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x10a2);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s10, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 160
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x10a2

    requires s0.stack[5] == 0x10ca

    requires s0.stack[10] == 0x66d

    requires s0.stack[12] == 0x51a

    requires s0.stack[15] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10a2;
      assert s1.Peek(5) == 0x10ca;
      assert s1.Peek(10) == 0x66d;
      assert s1.Peek(12) == 0x51a;
      assert s1.Peek(15) == 0x208;
      var s2 := Push2(s1, 0x0de3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s5, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xde3

    requires s0.stack[3] == 0x10a2

    requires s0.stack[7] == 0x10ca

    requires s0.stack[12] == 0x66d

    requires s0.stack[14] == 0x51a

    requires s0.stack[17] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde3;
      assert s1.Peek(3) == 0x10a2;
      assert s1.Peek(7) == 0x10ca;
      assert s1.Peek(12) == 0x66d;
      assert s1.Peek(14) == 0x51a;
      assert s1.Peek(17) == 0x208;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s6, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xde3

    requires s0.stack[6] == 0x10a2

    requires s0.stack[10] == 0x10ca

    requires s0.stack[15] == 0x66d

    requires s0.stack[17] == 0x51a

    requires s0.stack[20] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(6) == 0x10a2;
      assert s1.Peek(10) == 0x10ca;
      assert s1.Peek(15) == 0x66d;
      assert s1.Peek(17) == 0x51a;
      assert s1.Peek(20) == 0x208;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s218(s11, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xde3

    requires s0.stack[5] == 0x10a2

    requires s0.stack[9] == 0x10ca

    requires s0.stack[14] == 0x66d

    requires s0.stack[16] == 0x51a

    requires s0.stack[19] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(5) == 0x10a2;
      assert s1.Peek(9) == 0x10ca;
      assert s1.Peek(14) == 0x66d;
      assert s1.Peek(16) == 0x51a;
      assert s1.Peek(19) == 0x208;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s7, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 161
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x10a2

    requires s0.stack[6] == 0x10ca

    requires s0.stack[11] == 0x66d

    requires s0.stack[13] == 0x51a

    requires s0.stack[16] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10a2;
      assert s1.Peek(6) == 0x10ca;
      assert s1.Peek(11) == 0x66d;
      assert s1.Peek(13) == 0x51a;
      assert s1.Peek(16) == 0x208;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ded);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s221(s5, gas - 1)
      else
        ExecuteFromCFGNode_s220(s5, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 162
    * Starting at 0xdea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x10a2

    requires s0.stack[5] == 0x10ca

    requires s0.stack[10] == 0x66d

    requires s0.stack[12] == 0x51a

    requires s0.stack[15] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0x10a2;
      assert s1.Peek(6) == 0x10ca;
      assert s1.Peek(11) == 0x66d;
      assert s1.Peek(13) == 0x51a;
      assert s1.Peek(16) == 0x208;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 221
    * Segment Id for this node is: 163
    * Starting at 0xded
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x10a2

    requires s0.stack[5] == 0x10ca

    requires s0.stack[10] == 0x66d

    requires s0.stack[12] == 0x51a

    requires s0.stack[15] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10a2;
      assert s1.Peek(5) == 0x10ca;
      assert s1.Peek(10) == 0x66d;
      assert s1.Peek(12) == 0x51a;
      assert s1.Peek(15) == 0x208;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s3, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 231
    * Starting at 0x10a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x10ca

    requires s0.stack[8] == 0x66d

    requires s0.stack[10] == 0x51a

    requires s0.stack[13] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10ca;
      assert s1.Peek(8) == 0x66d;
      assert s1.Peek(10) == 0x51a;
      assert s1.Peek(13) == 0x208;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s6, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 236
    * Starting at 0x10ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x66d

    requires s0.stack[7] == 0x51a

    requires s0.stack[10] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x66d;
      assert s1.Peek(7) == 0x51a;
      assert s1.Peek(10) == 0x208;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s9, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 101
    * Starting at 0x66d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x51a

    requires s0.stack[5] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x51a;
      assert s1.Peek(5) == 0x208;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s5, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 91
    * Starting at 0x51a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x208;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := IsZero(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s226(s5, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 92
    * Starting at 0x533
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x533 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x208;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x057f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s228(s5, gas - 1)
      else
        ExecuteFromCFGNode_s227(s5, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 93
    * Starting at 0x53a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0x208;
      var s2 := Push20(s1, 0x7a250d5630b4cf539739df2c5dacb4c659f2488d);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := IsZero(s8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s228(s9, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 94
    * Starting at 0x57f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x208;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x05c7);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s4, gas - 1)
      else
        ExecuteFromCFGNode_s229(s4, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 95
    * Starting at 0x585
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x585 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0x208;
      var s2 := Push1(s1, 0x04);
      var s3 := Push0(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(5) == 0x208;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push0(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(4) == 0x208;
      var s22 := SStore(s21);
      var s23 := Pop(s22);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s230(s23, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 96
    * Starting at 0x5c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x208

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x208;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s3, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 48
    * Starting at 0x208
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x208 as nat
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

  /** Node 232
    * Segment Id for this node is: 42
    * Starting at 0x1be
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01d8);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x01d3);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x1d3;
      assert s11.Peek(3) == 0x1d8;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0e37);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s14, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 173
    * Starting at 0xe37
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1d3

    requires s0.stack[3] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1d3;
      assert s1.Peek(3) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0e4d);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s236(s11, gas - 1)
      else
        ExecuteFromCFGNode_s234(s11, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 174
    * Starting at 0xe45
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe45 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1d3

    requires s0.stack[5] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e4c);
      assert s1.Peek(0) == 0xe4c;
      assert s1.Peek(5) == 0x1d3;
      assert s1.Peek(6) == 0x1d8;
      var s2 := Push2(s1, 0x0da6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s3, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 156
    * Starting at 0xda6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xe4c

    requires s0.stack[5] == 0x1d3

    requires s0.stack[6] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe4c;
      assert s1.Peek(5) == 0x1d3;
      assert s1.Peek(6) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 236
    * Segment Id for this node is: 176
    * Starting at 0xe4d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1d3

    requires s0.stack[5] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1d3;
      assert s1.Peek(5) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0e5a);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0df0);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s9, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 164
    * Starting at 0xdf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe5a

    requires s0.stack[8] == 0x1d3

    requires s0.stack[9] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe5a;
      assert s1.Peek(8) == 0x1d3;
      assert s1.Peek(9) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0dfe);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s10, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 160
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xe5a

    requires s0.stack[11] == 0x1d3

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xe5a;
      assert s1.Peek(11) == 0x1d3;
      assert s1.Peek(12) == 0x1d8;
      var s2 := Push2(s1, 0x0de3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s5, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xde3

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0xe5a

    requires s0.stack[13] == 0x1d3

    requires s0.stack[14] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde3;
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0xe5a;
      assert s1.Peek(13) == 0x1d3;
      assert s1.Peek(14) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s240(s6, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xde3

    requires s0.stack[6] == 0xdfe

    requires s0.stack[10] == 0xe5a

    requires s0.stack[16] == 0x1d3

    requires s0.stack[17] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(6) == 0xdfe;
      assert s1.Peek(10) == 0xe5a;
      assert s1.Peek(16) == 0x1d3;
      assert s1.Peek(17) == 0x1d8;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s241(s11, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xde3

    requires s0.stack[5] == 0xdfe

    requires s0.stack[9] == 0xe5a

    requires s0.stack[15] == 0x1d3

    requires s0.stack[16] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(5) == 0xdfe;
      assert s1.Peek(9) == 0xe5a;
      assert s1.Peek(15) == 0x1d3;
      assert s1.Peek(16) == 0x1d8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s7, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 161
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0xe5a

    requires s0.stack[12] == 0x1d3

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xe5a;
      assert s1.Peek(12) == 0x1d3;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ded);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s244(s5, gas - 1)
      else
        ExecuteFromCFGNode_s243(s5, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 162
    * Starting at 0xdea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xe5a

    requires s0.stack[11] == 0x1d3

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xe5a;
      assert s1.Peek(12) == 0x1d3;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 244
    * Segment Id for this node is: 163
    * Starting at 0xded
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xe5a

    requires s0.stack[11] == 0x1d3

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xe5a;
      assert s1.Peek(11) == 0x1d3;
      assert s1.Peek(12) == 0x1d8;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s3, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 165
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe5a

    requires s0.stack[9] == 0x1d3

    requires s0.stack[10] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe5a;
      assert s1.Peek(9) == 0x1d3;
      assert s1.Peek(10) == 0x1d8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s6, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 177
    * Starting at 0xe5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1d3

    requires s0.stack[7] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1d3;
      assert s1.Peek(7) == 0x1d8;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0e6b);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0e23);
      assert s11.Peek(0) == 0xe23;
      assert s11.Peek(3) == 0xe6b;
      assert s11.Peek(9) == 0x1d3;
      assert s11.Peek(10) == 0x1d8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s247(s12, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 171
    * Starting at 0xe23
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe6b

    requires s0.stack[8] == 0x1d3

    requires s0.stack[9] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe6b;
      assert s1.Peek(8) == 0x1d3;
      assert s1.Peek(9) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0e31);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0e0d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s10, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 167
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0xe6b

    requires s0.stack[11] == 0x1d3

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe31;
      assert s1.Peek(5) == 0xe6b;
      assert s1.Peek(11) == 0x1d3;
      assert s1.Peek(12) == 0x1d8;
      var s2 := Push2(s1, 0x0e16);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s5, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xe16

    requires s0.stack[3] == 0xe31

    requires s0.stack[7] == 0xe6b

    requires s0.stack[13] == 0x1d3

    requires s0.stack[14] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe16;
      assert s1.Peek(3) == 0xe31;
      assert s1.Peek(7) == 0xe6b;
      assert s1.Peek(13) == 0x1d3;
      assert s1.Peek(14) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s9, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 168
    * Starting at 0xe16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xe31

    requires s0.stack[6] == 0xe6b

    requires s0.stack[12] == 0x1d3

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe31;
      assert s1.Peek(6) == 0xe6b;
      assert s1.Peek(12) == 0x1d3;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0e20);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s252(s5, gas - 1)
      else
        ExecuteFromCFGNode_s251(s5, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 169
    * Starting at 0xe1d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0xe6b

    requires s0.stack[11] == 0x1d3

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xe31;
      assert s1.Peek(6) == 0xe6b;
      assert s1.Peek(12) == 0x1d3;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 252
    * Segment Id for this node is: 170
    * Starting at 0xe20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0xe6b

    requires s0.stack[11] == 0x1d3

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe31;
      assert s1.Peek(5) == 0xe6b;
      assert s1.Peek(11) == 0x1d3;
      assert s1.Peek(12) == 0x1d8;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s3, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 172
    * Starting at 0xe31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe6b

    requires s0.stack[9] == 0x1d3

    requires s0.stack[10] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe6b;
      assert s1.Peek(9) == 0x1d3;
      assert s1.Peek(10) == 0x1d8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s6, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 178
    * Starting at 0xe6b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1d3

    requires s0.stack[7] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1d3;
      assert s1.Peek(7) == 0x1d8;
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
      ExecuteFromCFGNode_s255(s10, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 43
    * Starting at 0x1d3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1d8;
      var s2 := Push2(s1, 0x0435);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s256(s3, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 85
    * Starting at 0x435
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x435 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0441);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0a1d);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s8, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 128
    * Starting at 0xa1d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x441

    requires s0.stack[7] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x441;
      assert s1.Peek(7) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x04);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x441;
      assert s11.Peek(10) == 0x1d8;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x441;
      assert s21.Peek(9) == 0x1d8;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0aa1);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s29, gas - 1)
      else
        ExecuteFromCFGNode_s258(s29, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 129
    * Starting at 0xa67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x441

    requires s0.stack[8] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x441;
      assert s1.Peek(9) == 0x1d8;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a98);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x14e1);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s11, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 314
    * Starting at 0x14e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xa98

    requires s0.stack[6] == 0x441

    requires s0.stack[10] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa98;
      assert s1.Peek(6) == 0x441;
      assert s1.Peek(10) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0xa98;
      assert s11.Peek(9) == 0x441;
      assert s11.Peek(13) == 0x1d8;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x14f8);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x14bf);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s18, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 311
    * Starting at 0x14bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x14f8

    requires s0.stack[4] == 0xa98

    requires s0.stack[9] == 0x441

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x14f8;
      assert s1.Peek(4) == 0xa98;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x14cb);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s7, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x14cb

    requires s0.stack[5] == 0x14f8

    requires s0.stack[8] == 0xa98

    requires s0.stack[13] == 0x441

    requires s0.stack[17] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14cb;
      assert s1.Peek(5) == 0x14f8;
      assert s1.Peek(8) == 0xa98;
      assert s1.Peek(13) == 0x441;
      assert s1.Peek(17) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x14cb;
      assert s11.Peek(6) == 0x14f8;
      assert s11.Peek(9) == 0xa98;
      assert s11.Peek(14) == 0x441;
      assert s11.Peek(18) == 0x1d8;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s15, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 312
    * Starting at 0x14cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x14f8

    requires s0.stack[6] == 0xa98

    requires s0.stack[11] == 0x441

    requires s0.stack[15] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x14f8;
      assert s1.Peek(6) == 0xa98;
      assert s1.Peek(11) == 0x441;
      assert s1.Peek(15) == 0x1d8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x14d6);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1471);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s263(s7, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 310
    * Starting at 0x1471
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1471 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x14d6

    requires s0.stack[4] == 0x14f8

    requires s0.stack[7] == 0xa98

    requires s0.stack[12] == 0x441

    requires s0.stack[16] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x14d6;
      assert s1.Peek(4) == 0x14f8;
      assert s1.Peek(7) == 0xa98;
      assert s1.Peek(12) == 0x441;
      assert s1.Peek(16) == 0x1d8;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x616c616e63650000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x14d6;
      assert s11.Peek(4) == 0x14f8;
      assert s11.Peek(7) == 0xa98;
      assert s11.Peek(12) == 0x441;
      assert s11.Peek(16) == 0x1d8;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s13, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 313
    * Starting at 0x14d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x14f8

    requires s0.stack[5] == 0xa98

    requires s0.stack[10] == 0x441

    requires s0.stack[14] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14f8;
      assert s1.Peek(5) == 0xa98;
      assert s1.Peek(10) == 0x441;
      assert s1.Peek(14) == 0x1d8;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s10, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 315
    * Starting at 0x14f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xa98

    requires s0.stack[8] == 0x441

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa98;
      assert s1.Peek(8) == 0x441;
      assert s1.Peek(12) == 0x1d8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s7, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 130
    * Starting at 0xa98
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x441

    requires s0.stack[9] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x441;
      assert s1.Peek(9) == 0x1d8;
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

  /** Node 267
    * Segment Id for this node is: 131
    * Starting at 0xaa1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x441

    requires s0.stack[8] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x441;
      assert s1.Peek(8) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0b0f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s277(s10, gas - 1)
      else
        ExecuteFromCFGNode_s268(s10, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 132
    * Starting at 0xad5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x441

    requires s0.stack[8] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x441;
      assert s1.Peek(9) == 0x1d8;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0b06);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x156f);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s11, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 320
    * Starting at 0x156f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x156f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xb06

    requires s0.stack[6] == 0x441

    requires s0.stack[10] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb06;
      assert s1.Peek(6) == 0x441;
      assert s1.Peek(10) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0xb06;
      assert s11.Peek(9) == 0x441;
      assert s11.Peek(13) == 0x1d8;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1586);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x154d);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s18, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 317
    * Starting at 0x154d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1586

    requires s0.stack[4] == 0xb06

    requires s0.stack[9] == 0x441

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1586;
      assert s1.Peek(4) == 0xb06;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1559);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s7, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1559

    requires s0.stack[5] == 0x1586

    requires s0.stack[8] == 0xb06

    requires s0.stack[13] == 0x441

    requires s0.stack[17] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1559;
      assert s1.Peek(5) == 0x1586;
      assert s1.Peek(8) == 0xb06;
      assert s1.Peek(13) == 0x441;
      assert s1.Peek(17) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1559;
      assert s11.Peek(6) == 0x1586;
      assert s11.Peek(9) == 0xb06;
      assert s11.Peek(14) == 0x441;
      assert s11.Peek(18) == 0x1d8;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s15, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 318
    * Starting at 0x1559
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1559 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1586

    requires s0.stack[6] == 0xb06

    requires s0.stack[11] == 0x441

    requires s0.stack[15] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1586;
      assert s1.Peek(6) == 0xb06;
      assert s1.Peek(11) == 0x441;
      assert s1.Peek(15) == 0x1d8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1564);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x14ff);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s7, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 316
    * Starting at 0x14ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1564

    requires s0.stack[4] == 0x1586

    requires s0.stack[7] == 0xb06

    requires s0.stack[12] == 0x441

    requires s0.stack[16] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1564;
      assert s1.Peek(4) == 0x1586;
      assert s1.Peek(7) == 0xb06;
      assert s1.Peek(12) == 0x441;
      assert s1.Peek(16) == 0x1d8;
      var s2 := Push32(s1, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6472657373000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x1564;
      assert s11.Peek(4) == 0x1586;
      assert s11.Peek(7) == 0xb06;
      assert s11.Peek(12) == 0x441;
      assert s11.Peek(16) == 0x1d8;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s13, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 319
    * Starting at 0x1564
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1564 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x1586

    requires s0.stack[5] == 0xb06

    requires s0.stack[10] == 0x441

    requires s0.stack[14] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1586;
      assert s1.Peek(5) == 0xb06;
      assert s1.Peek(10) == 0x441;
      assert s1.Peek(14) == 0x1d8;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s10, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 321
    * Starting at 0x1586
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1586 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xb06

    requires s0.stack[8] == 0x441

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb06;
      assert s1.Peek(8) == 0x441;
      assert s1.Peek(12) == 0x1d8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s7, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 133
    * Starting at 0xb06
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x441

    requires s0.stack[9] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x441;
      assert s1.Peek(9) == 0x1d8;
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

  /** Node 277
    * Segment Id for this node is: 134
    * Starting at 0xb0f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x441

    requires s0.stack[8] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x441;
      assert s1.Peek(8) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0b7d);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s287(s10, gas - 1)
      else
        ExecuteFromCFGNode_s278(s10, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 135
    * Starting at 0xb43
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x441

    requires s0.stack[8] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x441;
      assert s1.Peek(9) == 0x1d8;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0b74);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x15fd);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s11, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 326
    * Starting at 0x15fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xb74

    requires s0.stack[6] == 0x441

    requires s0.stack[10] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb74;
      assert s1.Peek(6) == 0x441;
      assert s1.Peek(10) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0xb74;
      assert s11.Peek(9) == 0x441;
      assert s11.Peek(13) == 0x1d8;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1614);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x15db);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s18, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 323
    * Starting at 0x15db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1614

    requires s0.stack[4] == 0xb74

    requires s0.stack[9] == 0x441

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1614;
      assert s1.Peek(4) == 0xb74;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x15e7);
      var s4 := Push1(s3, 0x23);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s7, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x15e7

    requires s0.stack[5] == 0x1614

    requires s0.stack[8] == 0xb74

    requires s0.stack[13] == 0x441

    requires s0.stack[17] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15e7;
      assert s1.Peek(5) == 0x1614;
      assert s1.Peek(8) == 0xb74;
      assert s1.Peek(13) == 0x441;
      assert s1.Peek(17) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x15e7;
      assert s11.Peek(6) == 0x1614;
      assert s11.Peek(9) == 0xb74;
      assert s11.Peek(14) == 0x441;
      assert s11.Peek(18) == 0x1d8;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s15, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 324
    * Starting at 0x15e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1614

    requires s0.stack[6] == 0xb74

    requires s0.stack[11] == 0x441

    requires s0.stack[15] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1614;
      assert s1.Peek(6) == 0xb74;
      assert s1.Peek(11) == 0x441;
      assert s1.Peek(15) == 0x1d8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x15f2);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x158d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s7, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 322
    * Starting at 0x158d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x158d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x15f2

    requires s0.stack[4] == 0x1614

    requires s0.stack[7] == 0xb74

    requires s0.stack[12] == 0x441

    requires s0.stack[16] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x15f2;
      assert s1.Peek(4) == 0x1614;
      assert s1.Peek(7) == 0xb74;
      assert s1.Peek(12) == 0x441;
      assert s1.Peek(16) == 0x1d8;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6573730000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x15f2;
      assert s11.Peek(4) == 0x1614;
      assert s11.Peek(7) == 0xb74;
      assert s11.Peek(12) == 0x441;
      assert s11.Peek(16) == 0x1d8;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s13, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 325
    * Starting at 0x15f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x1614

    requires s0.stack[5] == 0xb74

    requires s0.stack[10] == 0x441

    requires s0.stack[14] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1614;
      assert s1.Peek(5) == 0xb74;
      assert s1.Peek(10) == 0x441;
      assert s1.Peek(14) == 0x1d8;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s10, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 327
    * Starting at 0x1614
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1614 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xb74

    requires s0.stack[8] == 0x441

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb74;
      assert s1.Peek(8) == 0x441;
      assert s1.Peek(12) == 0x1d8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s7, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 136
    * Starting at 0xb74
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x441

    requires s0.stack[9] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x441;
      assert s1.Peek(9) == 0x1d8;
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

  /** Node 287
    * Segment Id for this node is: 137
    * Starting at 0xb7d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x441

    requires s0.stack[8] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x441;
      assert s1.Peek(8) == 0x1d8;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x04);
      var s4 := Push0(s3);
      var s5 := Dup7(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x441;
      assert s11.Peek(11) == 0x1d8;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(6) == 0x441;
      assert s21.Peek(10) == 0x1d8;
      var s22 := Push2(s21, 0x0bc6);
      var s23 := Swap2(s22);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x143e);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s288(s26, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 304
    * Starting at 0x143e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xbc6

    requires s0.stack[7] == 0x441

    requires s0.stack[11] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbc6;
      assert s1.Peek(7) == 0x441;
      assert s1.Peek(11) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1448);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0e04);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s6, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1448

    requires s0.stack[5] == 0xbc6

    requires s0.stack[10] == 0x441

    requires s0.stack[14] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1448;
      assert s1.Peek(5) == 0xbc6;
      assert s1.Peek(10) == 0x441;
      assert s1.Peek(14) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s290(s9, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 305
    * Starting at 0x1448
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1448 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xbc6

    requires s0.stack[9] == 0x441

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbc6;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1453);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e04);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s291(s7, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1453

    requires s0.stack[5] == 0xbc6

    requires s0.stack[10] == 0x441

    requires s0.stack[14] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1453;
      assert s1.Peek(5) == 0xbc6;
      assert s1.Peek(10) == 0x441;
      assert s1.Peek(14) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s9, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 306
    * Starting at 0x1453
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1453 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xbc6

    requires s0.stack[9] == 0x441

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbc6;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup2(s8);
      var s10 := Dup2(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xbc6;
      assert s11.Peek(9) == 0x441;
      assert s11.Peek(13) == 0x1d8;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x146b);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s295(s14, gas - 1)
      else
        ExecuteFromCFGNode_s293(s14, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 307
    * Starting at 0x1463
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xbc6

    requires s0.stack[8] == 0x441

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x146a);
      assert s1.Peek(0) == 0x146a;
      assert s1.Peek(4) == 0xbc6;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s294(s3, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x146a

    requires s0.stack[4] == 0xbc6

    requires s0.stack[9] == 0x441

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x146a;
      assert s1.Peek(4) == 0xbc6;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 295
    * Segment Id for this node is: 309
    * Starting at 0x146b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xbc6

    requires s0.stack[8] == 0x441

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbc6;
      assert s1.Peek(8) == 0x441;
      assert s1.Peek(12) == 0x1d8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s6, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 138
    * Starting at 0xbc6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x441

    requires s0.stack[9] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x441;
      assert s1.Peek(9) == 0x1d8;
      var s2 := Push1(s1, 0x04);
      var s3 := Push0(s2);
      var s4 := Dup7(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(8) == 0x441;
      assert s11.Peek(12) == 0x1d8;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push0(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(7) == 0x441;
      assert s21.Peek(11) == 0x1d8;
      var s22 := SStore(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Push1(s24, 0x04);
      var s26 := Push0(s25);
      var s27 := Dup6(s26);
      var s28 := Push20(s27, 0xffffffffffffffffffffffffffffffffffffffff);
      var s29 := And(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(8) == 0x441;
      assert s31.Peek(12) == 0x1d8;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Swap1(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x20);
      var s40 := Add(s39);
      var s41 := Push0(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s297(s41, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 139
    * Starting at 0xc45
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc45 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x441

    requires s0.stack[11] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Keccak256(s0);
      assert s1.Peek(6) == 0x441;
      assert s1.Peek(10) == 0x1d8;
      var s2 := SLoad(s1);
      var s3 := Push2(s2, 0x0c50);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x161b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s298(s7, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 328
    * Starting at 0x161b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x161b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xc50

    requires s0.stack[7] == 0x441

    requires s0.stack[11] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc50;
      assert s1.Peek(7) == 0x441;
      assert s1.Peek(11) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1625);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0e04);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s6, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1625

    requires s0.stack[5] == 0xc50

    requires s0.stack[10] == 0x441

    requires s0.stack[14] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1625;
      assert s1.Peek(5) == 0xc50;
      assert s1.Peek(10) == 0x441;
      assert s1.Peek(14) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s300(s9, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 329
    * Starting at 0x1625
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1625 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xc50

    requires s0.stack[9] == 0x441

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc50;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1630);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e04);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s301(s7, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1630

    requires s0.stack[5] == 0xc50

    requires s0.stack[10] == 0x441

    requires s0.stack[14] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1630;
      assert s1.Peek(5) == 0xc50;
      assert s1.Peek(10) == 0x441;
      assert s1.Peek(14) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s302(s9, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 330
    * Starting at 0x1630
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1630 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xc50

    requires s0.stack[9] == 0x441

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc50;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xc50;
      assert s11.Peek(9) == 0x441;
      assert s11.Peek(13) == 0x1d8;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1648);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s305(s14, gas - 1)
      else
        ExecuteFromCFGNode_s303(s14, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 331
    * Starting at 0x1640
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1640 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xc50

    requires s0.stack[8] == 0x441

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1647);
      assert s1.Peek(0) == 0x1647;
      assert s1.Peek(4) == 0xc50;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s304(s3, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x1647

    requires s0.stack[4] == 0xc50

    requires s0.stack[9] == 0x441

    requires s0.stack[13] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1647;
      assert s1.Peek(4) == 0xc50;
      assert s1.Peek(9) == 0x441;
      assert s1.Peek(13) == 0x1d8;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 305
    * Segment Id for this node is: 333
    * Starting at 0x1648
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1648 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xc50

    requires s0.stack[8] == 0x441

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc50;
      assert s1.Peek(8) == 0x441;
      assert s1.Peek(12) == 0x1d8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s306(s6, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 140
    * Starting at 0xc50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x441

    requires s0.stack[9] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x441;
      assert s1.Peek(9) == 0x1d8;
      var s2 := Push1(s1, 0x04);
      var s3 := Push0(s2);
      var s4 := Dup6(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(8) == 0x441;
      assert s11.Peek(12) == 0x1d8;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push0(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(7) == 0x441;
      assert s21.Peek(11) == 0x1d8;
      var s22 := SStore(s21);
      var s23 := Pop(s22);
      var s24 := Dup3(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup5(s26);
      var s28 := Push20(s27, 0xffffffffffffffffffffffffffffffffffffffff);
      var s29 := And(s28);
      var s30 := Push32(s29, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s31 := Dup5(s30);
      assert s31.Peek(8) == 0x441;
      assert s31.Peek(12) == 0x1d8;
      var s32 := Push1(s31, 0x40);
      var s33 := MLoad(s32);
      var s34 := Push2(s33, 0x0cee);
      var s35 := Swap2(s34);
      var s36 := Swap1(s35);
      var s37 := Push2(s36, 0x0eb7);
      var s38 := Jump(s37);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s307(s38, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 186
    * Starting at 0xeb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xcee

    requires s0.stack[10] == 0x441

    requires s0.stack[14] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcee;
      assert s1.Peek(10) == 0x441;
      assert s1.Peek(14) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0eca);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xeca;
      assert s11.Peek(5) == 0xcee;
      assert s11.Peek(13) == 0x441;
      assert s11.Peek(17) == 0x1d8;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0ea8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s14, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 184
    * Starting at 0xea8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xeca

    requires s0.stack[6] == 0xcee

    requires s0.stack[14] == 0x441

    requires s0.stack[18] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeca;
      assert s1.Peek(6) == 0xcee;
      assert s1.Peek(14) == 0x441;
      assert s1.Peek(18) == 0x1d8;
      var s2 := Push2(s1, 0x0eb1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s309(s5, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0xeb1

    requires s0.stack[4] == 0xeca

    requires s0.stack[8] == 0xcee

    requires s0.stack[16] == 0x441

    requires s0.stack[20] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb1;
      assert s1.Peek(4) == 0xeca;
      assert s1.Peek(8) == 0xcee;
      assert s1.Peek(16) == 0x441;
      assert s1.Peek(20) == 0x1d8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s9, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 185
    * Starting at 0xeb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xeca

    requires s0.stack[7] == 0xcee

    requires s0.stack[15] == 0x441

    requires s0.stack[19] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xeca;
      assert s1.Peek(7) == 0xcee;
      assert s1.Peek(15) == 0x441;
      assert s1.Peek(19) == 0x1d8;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s6, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 187
    * Starting at 0xeca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xcee

    requires s0.stack[11] == 0x441

    requires s0.stack[15] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcee;
      assert s1.Peek(11) == 0x441;
      assert s1.Peek(15) == 0x1d8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s312(s6, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 141
    * Starting at 0xcee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x441

    requires s0.stack[12] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x441;
      assert s1.Peek(12) == 0x1d8;
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
      assert s11.Peek(1) == 0x441;
      assert s11.Peek(5) == 0x1d8;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s313(s13, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 86
    * Starting at 0x441
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x441 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1d8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1d8;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s314(s9, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 44
    * Starting at 0x1d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01e5);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0e8f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s8, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 182
    * Starting at 0xe8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1e5;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0ea2);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xea2;
      assert s11.Peek(5) == 0x1e5;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e80);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s14, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 180
    * Starting at 0xe80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xea2

    requires s0.stack[6] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xea2;
      assert s1.Peek(6) == 0x1e5;
      var s2 := Push2(s1, 0x0e89);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s317(s5, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 179
    * Starting at 0xe75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe89

    requires s0.stack[4] == 0xea2

    requires s0.stack[8] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe89;
      assert s1.Peek(4) == 0xea2;
      assert s1.Peek(8) == 0x1e5;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s318(s11, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 181
    * Starting at 0xe89
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xea2

    requires s0.stack[7] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xea2;
      assert s1.Peek(7) == 0x1e5;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s319(s6, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 183
    * Starting at 0xea2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1e5;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s320(s6, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 45
    * Starting at 0x1e5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e5 as nat
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

  /** Node 321
    * Segment Id for this node is: 39
    * Starting at 0x1a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01a8);
      var s3 := Push2(s2, 0x03a5);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s322(s4, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 76
    * Starting at 0x3a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1a8;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x03b4);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x103d);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s9, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 221
    * Starting at 0x103d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x3b4

    requires s0.stack[4] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b4;
      assert s1.Peek(4) == 0x1a8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x3b4;
      assert s11.Peek(7) == 0x1a8;
      var s12 := Push2(s11, 0x1054);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s325(s13, gas - 1)
      else
        ExecuteFromCFGNode_s324(s13, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 222
    * Starting at 0x104e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3b4

    requires s0.stack[6] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x3b4;
      assert s1.Peek(7) == 0x1a8;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s325(s5, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 223
    * Starting at 0x1054
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3b4

    requires s0.stack[6] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3b4;
      assert s1.Peek(6) == 0x1a8;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x1067);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s328(s8, gas - 1)
      else
        ExecuteFromCFGNode_s326(s8, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 224
    * Starting at 0x105f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3b4

    requires s0.stack[6] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1066);
      assert s1.Peek(0) == 0x1066;
      assert s1.Peek(4) == 0x3b4;
      assert s1.Peek(7) == 0x1a8;
      var s2 := Push2(s1, 0x1010);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s327(s3, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 220
    * Starting at 0x1010
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1010 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x1066

    requires s0.stack[4] == 0x3b4

    requires s0.stack[7] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1066;
      assert s1.Peek(4) == 0x3b4;
      assert s1.Peek(7) == 0x1a8;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 328
    * Segment Id for this node is: 226
    * Starting at 0x1067
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1067 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3b4

    requires s0.stack[6] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3b4;
      assert s1.Peek(6) == 0x1a8;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s329(s6, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 77
    * Starting at 0x3b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1a8;
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
      assert s11.Peek(4) == 0x1a8;
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
      assert s21.Peek(5) == 0x1a8;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x03e0);
      assert s31.Peek(0) == 0x3e0;
      assert s31.Peek(8) == 0x1a8;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x103d);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s34, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 221
    * Starting at 0x103d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x3e0

    requires s0.stack[8] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3e0;
      assert s1.Peek(8) == 0x1a8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x3e0;
      assert s11.Peek(11) == 0x1a8;
      var s12 := Push2(s11, 0x1054);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s332(s13, gas - 1)
      else
        ExecuteFromCFGNode_s331(s13, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 222
    * Starting at 0x104e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x3e0

    requires s0.stack[10] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x3e0;
      assert s1.Peek(11) == 0x1a8;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s332(s5, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 223
    * Starting at 0x1054
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x3e0

    requires s0.stack[10] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e0;
      assert s1.Peek(10) == 0x1a8;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x1067);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s335(s8, gas - 1)
      else
        ExecuteFromCFGNode_s333(s8, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 224
    * Starting at 0x105f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x3e0

    requires s0.stack[10] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1066);
      assert s1.Peek(0) == 0x1066;
      assert s1.Peek(4) == 0x3e0;
      assert s1.Peek(11) == 0x1a8;
      var s2 := Push2(s1, 0x1010);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s334(s3, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 220
    * Starting at 0x1010
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1010 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x1066

    requires s0.stack[4] == 0x3e0

    requires s0.stack[11] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1066;
      assert s1.Peek(4) == 0x3e0;
      assert s1.Peek(11) == 0x1a8;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 335
    * Segment Id for this node is: 226
    * Starting at 0x1067
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1067 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x3e0

    requires s0.stack[10] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e0;
      assert s1.Peek(10) == 0x1a8;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s6, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 78
    * Starting at 0x3e0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1a8;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x042b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s339(s5, gas - 1)
      else
        ExecuteFromCFGNode_s337(s5, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 79
    * Starting at 0x3e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0x1a8;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0402);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s356(s5, gas - 1)
      else
        ExecuteFromCFGNode_s338(s5, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 80
    * Starting at 0x3ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0x1a8;
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
      assert s11.Peek(7) == 0x1a8;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x042b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s14, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 84
    * Starting at 0x42b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1a8;
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
      ExecuteFromCFGNode_s340(s10, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 40
    * Starting at 0x1a8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01b5);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d86);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s8, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 154
    * Starting at 0xd86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b5;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(5) == 0x1b5;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0d9e);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0d4e);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s342(s19, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 149
    * Starting at 0xd4e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd9e

    requires s0.stack[6] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd9e;
      assert s1.Peek(6) == 0x1b5;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d58);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0cfc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s343(s6, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 142
    * Starting at 0xcfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xd58

    requires s0.stack[5] == 0xd9e

    requires s0.stack[9] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd58;
      assert s1.Peek(5) == 0xd9e;
      assert s1.Peek(9) == 0x1b5;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s10, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 150
    * Starting at 0xd58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xd9e

    requires s0.stack[8] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd9e;
      assert s1.Peek(8) == 0x1b5;
      var s2 := Push2(s1, 0x0d62);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s345(s6, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xd62

    requires s0.stack[7] == 0xd9e

    requires s0.stack[11] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd62;
      assert s1.Peek(7) == 0xd9e;
      assert s1.Peek(11) == 0x1b5;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xd62;
      assert s11.Peek(8) == 0xd9e;
      assert s11.Peek(12) == 0x1b5;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s346(s15, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 151
    * Starting at 0xd62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xd9e

    requires s0.stack[9] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd9e;
      assert s1.Peek(9) == 0x1b5;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0d72);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0d16);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s11, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 144
    * Starting at 0xd16
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xd72

    requires s0.stack[8] == 0xd9e

    requires s0.stack[12] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd72;
      assert s1.Peek(8) == 0xd9e;
      assert s1.Peek(12) == 0x1b5;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s348(s2, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 145
    * Starting at 0xd18
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd72

    requires s0.stack[9] == 0xd9e

    requires s0.stack[13] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd72;
      assert s1.Peek(9) == 0xd9e;
      assert s1.Peek(13) == 0x1b5;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0d33);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s350(s7, gas - 1)
      else
        ExecuteFromCFGNode_s349(s7, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 146
    * Starting at 0xd21
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd21 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd72

    requires s0.stack[9] == 0xd9e

    requires s0.stack[13] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xd72;
      assert s1.Peek(10) == 0xd9e;
      assert s1.Peek(14) == 0x1b5;
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
      assert s11.Peek(5) == 0xd72;
      assert s11.Peek(10) == 0xd9e;
      assert s11.Peek(14) == 0x1b5;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0d18);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s348(s15, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 147
    * Starting at 0xd33
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd72

    requires s0.stack[9] == 0xd9e

    requires s0.stack[13] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd72;
      assert s1.Peek(9) == 0xd9e;
      assert s1.Peek(13) == 0x1b5;
      var s2 := Push0(s1);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s351(s11, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 152
    * Starting at 0xd72
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xd9e

    requires s0.stack[8] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd9e;
      assert s1.Peek(8) == 0x1b5;
      var s2 := Push2(s1, 0x0d7b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d3e);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s5, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 148
    * Starting at 0xd3e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xd7b

    requires s0.stack[6] == 0xd9e

    requires s0.stack[10] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd7b;
      assert s1.Peek(6) == 0xd9e;
      assert s1.Peek(10) == 0x1b5;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xd7b;
      assert s11.Peek(7) == 0xd9e;
      assert s11.Peek(11) == 0x1b5;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s14, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 153
    * Starting at 0xd7b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xd9e

    requires s0.stack[9] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd9e;
      assert s1.Peek(9) == 0x1b5;
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
      ExecuteFromCFGNode_s354(s11, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 155
    * Starting at 0xd9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1b5;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s8, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 41
    * Starting at 0x1b5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b5 as nat
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

  /** Node 356
    * Segment Id for this node is: 81
    * Starting at 0x402
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x402 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1a8;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Push0(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Push0(s8);
      var s10 := Keccak256(s9);
      var s11 := Swap1(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s357(s11, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 82
    * Starting at 0x40e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1a8;
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
      assert s11.Peek(7) == 0x1a8;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x040e);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s357(s16, gas - 1)
      else
        ExecuteFromCFGNode_s358(s16, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 83
    * Starting at 0x422
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0x1a8;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s339(s8, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 11
    * Starting at 0x6f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f as nat
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
      var s5 := Push2(s4, 0x00b6);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s622(s6, gas - 1)
      else
        ExecuteFromCFGNode_s360(s6, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 12
    * Starting at 0x7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00d4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s561(s5, gas - 1)
      else
        ExecuteFromCFGNode_s361(s5, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 13
    * Starting at 0x86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0104);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s552(s5, gas - 1)
      else
        ExecuteFromCFGNode_s362(s5, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 14
    * Starting at 0x91
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0122);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s398(s5, gas - 1)
      else
        ExecuteFromCFGNode_s363(s5, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 15
    * Starting at 0x9c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0152);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s389(s5, gas - 1)
      else
        ExecuteFromCFGNode_s364(s5, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 16
    * Starting at 0xa7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0170);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s365(s5, gas - 1)
      else
        ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 35
    * Starting at 0x170
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x170 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x018a);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0185);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x185;
      assert s11.Peek(3) == 0x18a;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f54);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s366(s14, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 200
    * Starting at 0xf54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x185

    requires s0.stack[3] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x185;
      assert s1.Peek(3) == 0x18a;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0f69);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s369(s10, gas - 1)
      else
        ExecuteFromCFGNode_s367(s10, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 201
    * Starting at 0xf61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x185

    requires s0.stack[4] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f68);
      assert s1.Peek(0) == 0xf68;
      assert s1.Peek(4) == 0x185;
      assert s1.Peek(5) == 0x18a;
      var s2 := Push2(s1, 0x0da6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s3, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 156
    * Starting at 0xda6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0xf68

    requires s0.stack[4] == 0x185

    requires s0.stack[5] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf68;
      assert s1.Peek(4) == 0x185;
      assert s1.Peek(5) == 0x18a;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 369
    * Segment Id for this node is: 203
    * Starting at 0xf69
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x185

    requires s0.stack[4] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x185;
      assert s1.Peek(4) == 0x18a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f76);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0df0);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s9, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 164
    * Starting at 0xdf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xf76

    requires s0.stack[7] == 0x185

    requires s0.stack[8] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf76;
      assert s1.Peek(7) == 0x185;
      assert s1.Peek(8) == 0x18a;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0dfe);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s371(s10, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 160
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xf76

    requires s0.stack[10] == 0x185

    requires s0.stack[11] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xf76;
      assert s1.Peek(10) == 0x185;
      assert s1.Peek(11) == 0x18a;
      var s2 := Push2(s1, 0x0de3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s5, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xde3

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0xf76

    requires s0.stack[12] == 0x185

    requires s0.stack[13] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde3;
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0xf76;
      assert s1.Peek(12) == 0x185;
      assert s1.Peek(13) == 0x18a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s6, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xde3

    requires s0.stack[6] == 0xdfe

    requires s0.stack[10] == 0xf76

    requires s0.stack[15] == 0x185

    requires s0.stack[16] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(6) == 0xdfe;
      assert s1.Peek(10) == 0xf76;
      assert s1.Peek(15) == 0x185;
      assert s1.Peek(16) == 0x18a;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s374(s11, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xde3

    requires s0.stack[5] == 0xdfe

    requires s0.stack[9] == 0xf76

    requires s0.stack[14] == 0x185

    requires s0.stack[15] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(5) == 0xdfe;
      assert s1.Peek(9) == 0xf76;
      assert s1.Peek(14) == 0x185;
      assert s1.Peek(15) == 0x18a;
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
    * Segment Id for this node is: 161
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0xf76

    requires s0.stack[11] == 0x185

    requires s0.stack[12] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xf76;
      assert s1.Peek(11) == 0x185;
      assert s1.Peek(12) == 0x18a;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ded);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s377(s5, gas - 1)
      else
        ExecuteFromCFGNode_s376(s5, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 162
    * Starting at 0xdea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xf76

    requires s0.stack[10] == 0x185

    requires s0.stack[11] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xf76;
      assert s1.Peek(11) == 0x185;
      assert s1.Peek(12) == 0x18a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 377
    * Segment Id for this node is: 163
    * Starting at 0xded
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xf76

    requires s0.stack[10] == 0x185

    requires s0.stack[11] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xf76;
      assert s1.Peek(10) == 0x185;
      assert s1.Peek(11) == 0x18a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s378(s3, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 165
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xf76

    requires s0.stack[8] == 0x185

    requires s0.stack[9] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf76;
      assert s1.Peek(8) == 0x185;
      assert s1.Peek(9) == 0x18a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s379(s6, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 204
    * Starting at 0xf76
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf76 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x185

    requires s0.stack[6] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x185;
      assert s1.Peek(6) == 0x18a;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s9, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 36
    * Starting at 0x185
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x185 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x18a;
      var s2 := Push2(s1, 0x035f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s381(s3, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 75
    * Starting at 0x35f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x18a;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x04);
      var s4 := Push0(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x18a;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(3) == 0x18a;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Swap2(s23);
      var s25 := Swap1(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s27, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 37
    * Starting at 0x18a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0197);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0eb7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s8, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 186
    * Starting at 0xeb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x197;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0eca);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xeca;
      assert s11.Peek(5) == 0x197;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0ea8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s384(s14, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 184
    * Starting at 0xea8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xeca

    requires s0.stack[6] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeca;
      assert s1.Peek(6) == 0x197;
      var s2 := Push2(s1, 0x0eb1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s5, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xeb1

    requires s0.stack[4] == 0xeca

    requires s0.stack[8] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb1;
      assert s1.Peek(4) == 0xeca;
      assert s1.Peek(8) == 0x197;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s9, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 185
    * Starting at 0xeb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xeca

    requires s0.stack[7] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xeca;
      assert s1.Peek(7) == 0x197;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s387(s6, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 187
    * Starting at 0xeca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x197;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s388(s6, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 38
    * Starting at 0x197
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x197 as nat
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

  /** Node 389
    * Segment Id for this node is: 32
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x015a);
      var s3 := Push2(s2, 0x0349);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s390(s4, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 74
    * Starting at 0x349
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x349 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x15a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x15a;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Push1(s3, 0x14);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x15a;
      var s12 := Push1(s11, 0xff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s391(s17, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 33
    * Starting at 0x15a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0167);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0f3b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s392(s8, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 198
    * Starting at 0xf3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x167;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0f4e);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xf4e;
      assert s11.Peek(5) == 0x167;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0f2c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s14, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 196
    * Starting at 0xf2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xf4e

    requires s0.stack[6] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf4e;
      assert s1.Peek(6) == 0x167;
      var s2 := Push2(s1, 0x0f35);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0f20);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s5, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 195
    * Starting at 0xf20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf35

    requires s0.stack[4] == 0xf4e

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf35;
      assert s1.Peek(4) == 0xf4e;
      assert s1.Peek(8) == 0x167;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s395(s11, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 197
    * Starting at 0xf35
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xf4e

    requires s0.stack[7] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf4e;
      assert s1.Peek(7) == 0x167;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s6, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 199
    * Starting at 0xf4e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x167;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s397(s6, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 34
    * Starting at 0x167
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x167 as nat
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

  /** Node 398
    * Segment Id for this node is: 28
    * Starting at 0x122
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x013c);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0137);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x137;
      assert s11.Peek(3) == 0x13c;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0ed0);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s399(s14, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 188
    * Starting at 0xed0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x137

    requires s0.stack[3] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x137;
      assert s1.Peek(3) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0ee7);
      assert s11.Peek(0) == 0xee7;
      assert s11.Peek(7) == 0x137;
      assert s11.Peek(8) == 0x13c;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s402(s12, gas - 1)
      else
        ExecuteFromCFGNode_s400(s12, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 189
    * Starting at 0xedf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x137

    requires s0.stack[6] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ee6);
      assert s1.Peek(0) == 0xee6;
      assert s1.Peek(6) == 0x137;
      assert s1.Peek(7) == 0x13c;
      var s2 := Push2(s1, 0x0da6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s401(s3, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 156
    * Starting at 0xda6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xee6

    requires s0.stack[6] == 0x137

    requires s0.stack[7] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xee6;
      assert s1.Peek(6) == 0x137;
      assert s1.Peek(7) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 402
    * Segment Id for this node is: 191
    * Starting at 0xee7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x137

    requires s0.stack[6] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x137;
      assert s1.Peek(6) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0ef4);
      var s4 := Dup7(s3);
      var s5 := Dup3(s4);
      var s6 := Dup8(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0df0);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s403(s9, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 164
    * Starting at 0xdf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xef4

    requires s0.stack[9] == 0x137

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xef4;
      assert s1.Peek(9) == 0x137;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0dfe);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s10, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 160
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xef4

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xef4;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push2(s1, 0x0de3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s5, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xde3

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0xef4

    requires s0.stack[14] == 0x137

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde3;
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0xef4;
      assert s1.Peek(14) == 0x137;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s6, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xde3

    requires s0.stack[6] == 0xdfe

    requires s0.stack[10] == 0xef4

    requires s0.stack[17] == 0x137

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(6) == 0xdfe;
      assert s1.Peek(10) == 0xef4;
      assert s1.Peek(17) == 0x137;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s407(s11, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xde3

    requires s0.stack[5] == 0xdfe

    requires s0.stack[9] == 0xef4

    requires s0.stack[16] == 0x137

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(5) == 0xdfe;
      assert s1.Peek(9) == 0xef4;
      assert s1.Peek(16) == 0x137;
      assert s1.Peek(17) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s7, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 161
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0xef4

    requires s0.stack[13] == 0x137

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xef4;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ded);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s410(s5, gas - 1)
      else
        ExecuteFromCFGNode_s409(s5, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 162
    * Starting at 0xdea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xef4

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xef4;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 410
    * Segment Id for this node is: 163
    * Starting at 0xded
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xef4

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xef4;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s411(s3, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 165
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xef4

    requires s0.stack[10] == 0x137

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xef4;
      assert s1.Peek(10) == 0x137;
      assert s1.Peek(11) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s412(s6, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 192
    * Starting at 0xef4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x137

    requires s0.stack[8] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x137;
      assert s1.Peek(8) == 0x13c;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0f05);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0df0);
      assert s11.Peek(0) == 0xdf0;
      assert s11.Peek(3) == 0xf05;
      assert s11.Peek(10) == 0x137;
      assert s11.Peek(11) == 0x13c;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s413(s12, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 164
    * Starting at 0xdf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xf05

    requires s0.stack[9] == 0x137

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf05;
      assert s1.Peek(9) == 0x137;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0dfe);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s414(s10, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 160
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xf05

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xf05;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push2(s1, 0x0de3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s5, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xde3

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0xf05

    requires s0.stack[14] == 0x137

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde3;
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0xf05;
      assert s1.Peek(14) == 0x137;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s416(s6, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xde3

    requires s0.stack[6] == 0xdfe

    requires s0.stack[10] == 0xf05

    requires s0.stack[17] == 0x137

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(6) == 0xdfe;
      assert s1.Peek(10) == 0xf05;
      assert s1.Peek(17) == 0x137;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push0(s1);
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
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xde3

    requires s0.stack[5] == 0xdfe

    requires s0.stack[9] == 0xf05

    requires s0.stack[16] == 0x137

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(5) == 0xdfe;
      assert s1.Peek(9) == 0xf05;
      assert s1.Peek(16) == 0x137;
      assert s1.Peek(17) == 0x13c;
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
    * Segment Id for this node is: 161
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0xf05

    requires s0.stack[13] == 0x137

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xf05;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ded);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s420(s5, gas - 1)
      else
        ExecuteFromCFGNode_s419(s5, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 162
    * Starting at 0xdea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xf05

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xf05;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 420
    * Segment Id for this node is: 163
    * Starting at 0xded
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xf05

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xf05;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s3, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 165
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xf05

    requires s0.stack[10] == 0x137

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf05;
      assert s1.Peek(10) == 0x137;
      assert s1.Peek(11) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s422(s6, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 193
    * Starting at 0xf05
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x137

    requires s0.stack[8] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x137;
      assert s1.Peek(8) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Push2(s5, 0x0f16);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0e23);
      assert s11.Peek(0) == 0xe23;
      assert s11.Peek(3) == 0xf16;
      assert s11.Peek(10) == 0x137;
      assert s11.Peek(11) == 0x13c;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s423(s12, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 171
    * Starting at 0xe23
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xf16

    requires s0.stack[9] == 0x137

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf16;
      assert s1.Peek(9) == 0x137;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0e31);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0e0d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s424(s10, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 167
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0xf16

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe31;
      assert s1.Peek(5) == 0xf16;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push2(s1, 0x0e16);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s425(s5, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xe16

    requires s0.stack[3] == 0xe31

    requires s0.stack[7] == 0xf16

    requires s0.stack[14] == 0x137

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe16;
      assert s1.Peek(3) == 0xe31;
      assert s1.Peek(7) == 0xf16;
      assert s1.Peek(14) == 0x137;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s426(s9, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 168
    * Starting at 0xe16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xe31

    requires s0.stack[6] == 0xf16

    requires s0.stack[13] == 0x137

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe31;
      assert s1.Peek(6) == 0xf16;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0e20);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s428(s5, gas - 1)
      else
        ExecuteFromCFGNode_s427(s5, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 169
    * Starting at 0xe1d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0xf16

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xe31;
      assert s1.Peek(6) == 0xf16;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 428
    * Segment Id for this node is: 170
    * Starting at 0xe20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0xf16

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe31;
      assert s1.Peek(5) == 0xf16;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s429(s3, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 172
    * Starting at 0xe31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xf16

    requires s0.stack[10] == 0x137

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf16;
      assert s1.Peek(10) == 0x137;
      assert s1.Peek(11) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s430(s6, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 194
    * Starting at 0xf16
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x137

    requires s0.stack[8] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x137;
      assert s1.Peek(8) == 0x13c;
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
      ExecuteFromCFGNode_s431(s10, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 29
    * Starting at 0x137
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x137 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13c;
      var s2 := Push2(s1, 0x0322);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s432(s3, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 71
    * Starting at 0x322
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x322 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Caller(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0332);
      var s8 := Dup6(s7);
      var s9 := Dup3(s8);
      var s10 := Dup6(s9);
      var s11 := Push2(s10, 0x0989);
      assert s11.Peek(0) == 0x989;
      assert s11.Peek(4) == 0x332;
      assert s11.Peek(10) == 0x13c;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s433(s12, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 119
    * Starting at 0x989
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x989 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x332

    requires s0.stack[9] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x332;
      assert s1.Peek(9) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0994);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0672);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s434(s7, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 102
    * Starting at 0x672
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x672 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x994

    requires s0.stack[7] == 0x332

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x994;
      assert s1.Peek(7) == 0x332;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x994;
      assert s11.Peek(10) == 0x332;
      assert s11.Peek(16) == 0x13c;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(5) == 0x994;
      assert s21.Peek(10) == 0x332;
      assert s21.Peek(16) == 0x13c;
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
      assert s31.Peek(5) == 0x994;
      assert s31.Peek(10) == 0x332;
      assert s31.Peek(16) == 0x13c;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s435(s41, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 103
    * Starting at 0x6f0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x994

    requires s0.stack[8] == 0x332

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x994;
      assert s1.Peek(8) == 0x332;
      assert s1.Peek(14) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s436(s4, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 120
    * Starting at 0x994
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x994 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x332

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x332;
      assert s1.Peek(11) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x0a17);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s486(s8, gas - 1)
      else
        ExecuteFromCFGNode_s437(s8, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 121
    * Starting at 0x9be
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x332

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x332;
      assert s1.Peek(11) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0a00);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s447(s6, gas - 1)
      else
        ExecuteFromCFGNode_s438(s6, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 122
    * Starting at 0x9c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x332

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x332;
      assert s1.Peek(11) == 0x13c;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x09f7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1420);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s11, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 302
    * Starting at 0x1420
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1420 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x9f7

    requires s0.stack[6] == 0x332

    requires s0.stack[12] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9f7;
      assert s1.Peek(6) == 0x332;
      assert s1.Peek(12) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x9f7;
      assert s11.Peek(9) == 0x332;
      assert s11.Peek(15) == 0x13c;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1437);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x13fe);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s440(s18, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 299
    * Starting at 0x13fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x1437

    requires s0.stack[4] == 0x9f7

    requires s0.stack[9] == 0x332

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1437;
      assert s1.Peek(4) == 0x9f7;
      assert s1.Peek(9) == 0x332;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x140a);
      var s4 := Push1(s3, 0x1d);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s441(s7, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x140a

    requires s0.stack[5] == 0x1437

    requires s0.stack[8] == 0x9f7

    requires s0.stack[13] == 0x332

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x140a;
      assert s1.Peek(5) == 0x1437;
      assert s1.Peek(8) == 0x9f7;
      assert s1.Peek(13) == 0x332;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x140a;
      assert s11.Peek(6) == 0x1437;
      assert s11.Peek(9) == 0x9f7;
      assert s11.Peek(14) == 0x332;
      assert s11.Peek(20) == 0x13c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s15, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 300
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x1437

    requires s0.stack[6] == 0x9f7

    requires s0.stack[11] == 0x332

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1437;
      assert s1.Peek(6) == 0x9f7;
      assert s1.Peek(11) == 0x332;
      assert s1.Peek(17) == 0x13c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1415);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x13d6);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s7, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 298
    * Starting at 0x13d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x1415

    requires s0.stack[4] == 0x1437

    requires s0.stack[7] == 0x9f7

    requires s0.stack[12] == 0x332

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1415;
      assert s1.Peek(4) == 0x1437;
      assert s1.Peek(7) == 0x9f7;
      assert s1.Peek(12) == 0x332;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push32(s1, 0x45524332303a20696e73756666696369656e7420616c6c6f77616e6365000000);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s444(s8, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 301
    * Starting at 0x1415
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1415 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x1437

    requires s0.stack[5] == 0x9f7

    requires s0.stack[10] == 0x332

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1437;
      assert s1.Peek(5) == 0x9f7;
      assert s1.Peek(10) == 0x332;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s10, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 303
    * Starting at 0x1437
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1437 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x9f7

    requires s0.stack[8] == 0x332

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9f7;
      assert s1.Peek(8) == 0x332;
      assert s1.Peek(14) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s7, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 123
    * Starting at 0x9f7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x332

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x332;
      assert s1.Peek(11) == 0x13c;
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

  /** Node 447
    * Segment Id for this node is: 124
    * Starting at 0xa00
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x332

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x332;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push2(s1, 0x0a16);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0a11);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x143e);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s448(s11, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 304
    * Starting at 0x143e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xa11

    requires s0.stack[5] == 0xa16

    requires s0.stack[10] == 0x332

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa11;
      assert s1.Peek(5) == 0xa16;
      assert s1.Peek(10) == 0x332;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1448);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0e04);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s449(s6, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1448

    requires s0.stack[5] == 0xa11

    requires s0.stack[8] == 0xa16

    requires s0.stack[13] == 0x332

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1448;
      assert s1.Peek(5) == 0xa11;
      assert s1.Peek(8) == 0xa16;
      assert s1.Peek(13) == 0x332;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s9, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 305
    * Starting at 0x1448
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1448 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xa11

    requires s0.stack[7] == 0xa16

    requires s0.stack[12] == 0x332

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa11;
      assert s1.Peek(7) == 0xa16;
      assert s1.Peek(12) == 0x332;
      assert s1.Peek(18) == 0x13c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1453);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e04);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s451(s7, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1453

    requires s0.stack[5] == 0xa11

    requires s0.stack[8] == 0xa16

    requires s0.stack[13] == 0x332

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1453;
      assert s1.Peek(5) == 0xa11;
      assert s1.Peek(8) == 0xa16;
      assert s1.Peek(13) == 0x332;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s9, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 306
    * Starting at 0x1453
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1453 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xa11

    requires s0.stack[7] == 0xa16

    requires s0.stack[12] == 0x332

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa11;
      assert s1.Peek(7) == 0xa16;
      assert s1.Peek(12) == 0x332;
      assert s1.Peek(18) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup2(s8);
      var s10 := Dup2(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xa11;
      assert s11.Peek(7) == 0xa16;
      assert s11.Peek(12) == 0x332;
      assert s11.Peek(18) == 0x13c;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x146b);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s455(s14, gas - 1)
      else
        ExecuteFromCFGNode_s453(s14, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 307
    * Starting at 0x1463
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xa11

    requires s0.stack[6] == 0xa16

    requires s0.stack[11] == 0x332

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x146a);
      assert s1.Peek(0) == 0x146a;
      assert s1.Peek(4) == 0xa11;
      assert s1.Peek(7) == 0xa16;
      assert s1.Peek(12) == 0x332;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s454(s3, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x146a

    requires s0.stack[4] == 0xa11

    requires s0.stack[7] == 0xa16

    requires s0.stack[12] == 0x332

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x146a;
      assert s1.Peek(4) == 0xa11;
      assert s1.Peek(7) == 0xa16;
      assert s1.Peek(12) == 0x332;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 455
    * Segment Id for this node is: 309
    * Starting at 0x146b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xa11

    requires s0.stack[6] == 0xa16

    requires s0.stack[11] == 0x332

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa11;
      assert s1.Peek(6) == 0xa16;
      assert s1.Peek(11) == 0x332;
      assert s1.Peek(17) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s456(s6, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 125
    * Starting at 0xa11
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xa16

    requires s0.stack[8] == 0x332

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa16;
      assert s1.Peek(8) == 0x332;
      assert s1.Peek(14) == 0x13c;
      var s2 := Push2(s1, 0x07c6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s457(s3, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 110
    * Starting at 0x7c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xa16

    requires s0.stack[8] == 0x332

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa16;
      assert s1.Peek(8) == 0x332;
      assert s1.Peek(14) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0834);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s467(s10, gas - 1)
      else
        ExecuteFromCFGNode_s458(s10, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 111
    * Starting at 0x7fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xa16

    requires s0.stack[8] == 0x332

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xa16;
      assert s1.Peek(9) == 0x332;
      assert s1.Peek(15) == 0x13c;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x082b);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x132a);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s11, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 290
    * Starting at 0x132a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x82b

    requires s0.stack[5] == 0xa16

    requires s0.stack[10] == 0x332

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x82b;
      assert s1.Peek(5) == 0xa16;
      assert s1.Peek(10) == 0x332;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x82b;
      assert s11.Peek(8) == 0xa16;
      assert s11.Peek(13) == 0x332;
      assert s11.Peek(19) == 0x13c;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1341);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1308);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s18, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 287
    * Starting at 0x1308
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1308 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1341

    requires s0.stack[4] == 0x82b

    requires s0.stack[8] == 0xa16

    requires s0.stack[13] == 0x332

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1341;
      assert s1.Peek(4) == 0x82b;
      assert s1.Peek(8) == 0xa16;
      assert s1.Peek(13) == 0x332;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1314);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s7, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x1314

    requires s0.stack[5] == 0x1341

    requires s0.stack[8] == 0x82b

    requires s0.stack[12] == 0xa16

    requires s0.stack[17] == 0x332

    requires s0.stack[23] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1314;
      assert s1.Peek(5) == 0x1341;
      assert s1.Peek(8) == 0x82b;
      assert s1.Peek(12) == 0xa16;
      assert s1.Peek(17) == 0x332;
      assert s1.Peek(23) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1314;
      assert s11.Peek(6) == 0x1341;
      assert s11.Peek(9) == 0x82b;
      assert s11.Peek(13) == 0xa16;
      assert s11.Peek(18) == 0x332;
      assert s11.Peek(24) == 0x13c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s15, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 288
    * Starting at 0x1314
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1314 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x1341

    requires s0.stack[6] == 0x82b

    requires s0.stack[10] == 0xa16

    requires s0.stack[15] == 0x332

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1341;
      assert s1.Peek(6) == 0x82b;
      assert s1.Peek(10) == 0xa16;
      assert s1.Peek(15) == 0x332;
      assert s1.Peek(21) == 0x13c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x131f);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x12ba);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s463(s7, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 286
    * Starting at 0x12ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x131f

    requires s0.stack[4] == 0x1341

    requires s0.stack[7] == 0x82b

    requires s0.stack[11] == 0xa16

    requires s0.stack[16] == 0x332

    requires s0.stack[22] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x131f;
      assert s1.Peek(4) == 0x1341;
      assert s1.Peek(7) == 0x82b;
      assert s1.Peek(11) == 0xa16;
      assert s1.Peek(16) == 0x332;
      assert s1.Peek(22) == 0x13c;
      var s2 := Push32(s1, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x131f;
      assert s11.Peek(4) == 0x1341;
      assert s11.Peek(7) == 0x82b;
      assert s11.Peek(11) == 0xa16;
      assert s11.Peek(16) == 0x332;
      assert s11.Peek(22) == 0x13c;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s13, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 289
    * Starting at 0x131f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x1341

    requires s0.stack[5] == 0x82b

    requires s0.stack[9] == 0xa16

    requires s0.stack[14] == 0x332

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1341;
      assert s1.Peek(5) == 0x82b;
      assert s1.Peek(9) == 0xa16;
      assert s1.Peek(14) == 0x332;
      assert s1.Peek(20) == 0x13c;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s465(s10, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 291
    * Starting at 0x1341
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1341 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x82b

    requires s0.stack[7] == 0xa16

    requires s0.stack[12] == 0x332

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x82b;
      assert s1.Peek(7) == 0xa16;
      assert s1.Peek(12) == 0x332;
      assert s1.Peek(18) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s466(s7, gas - 1)
  }

  /** Node 466
    * Segment Id for this node is: 112
    * Starting at 0x82b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xa16

    requires s0.stack[9] == 0x332

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa16;
      assert s1.Peek(9) == 0x332;
      assert s1.Peek(15) == 0x13c;
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

  /** Node 467
    * Segment Id for this node is: 113
    * Starting at 0x834
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x834 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xa16

    requires s0.stack[8] == 0x332

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa16;
      assert s1.Peek(8) == 0x332;
      assert s1.Peek(14) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x08a2);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s477(s10, gas - 1)
      else
        ExecuteFromCFGNode_s468(s10, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 114
    * Starting at 0x868
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x868 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xa16

    requires s0.stack[8] == 0x332

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xa16;
      assert s1.Peek(9) == 0x332;
      assert s1.Peek(15) == 0x13c;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0899);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x13b8);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s11, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 296
    * Starting at 0x13b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x899

    requires s0.stack[5] == 0xa16

    requires s0.stack[10] == 0x332

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x899;
      assert s1.Peek(5) == 0xa16;
      assert s1.Peek(10) == 0x332;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x899;
      assert s11.Peek(8) == 0xa16;
      assert s11.Peek(13) == 0x332;
      assert s11.Peek(19) == 0x13c;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x13cf);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1396);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s470(s18, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 293
    * Starting at 0x1396
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1396 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x13cf

    requires s0.stack[4] == 0x899

    requires s0.stack[8] == 0xa16

    requires s0.stack[13] == 0x332

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13cf;
      assert s1.Peek(4) == 0x899;
      assert s1.Peek(8) == 0xa16;
      assert s1.Peek(13) == 0x332;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x13a2);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s471(s7, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x13a2

    requires s0.stack[5] == 0x13cf

    requires s0.stack[8] == 0x899

    requires s0.stack[12] == 0xa16

    requires s0.stack[17] == 0x332

    requires s0.stack[23] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13a2;
      assert s1.Peek(5) == 0x13cf;
      assert s1.Peek(8) == 0x899;
      assert s1.Peek(12) == 0xa16;
      assert s1.Peek(17) == 0x332;
      assert s1.Peek(23) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x13a2;
      assert s11.Peek(6) == 0x13cf;
      assert s11.Peek(9) == 0x899;
      assert s11.Peek(13) == 0xa16;
      assert s11.Peek(18) == 0x332;
      assert s11.Peek(24) == 0x13c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s15, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 294
    * Starting at 0x13a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x13cf

    requires s0.stack[6] == 0x899

    requires s0.stack[10] == 0xa16

    requires s0.stack[15] == 0x332

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13cf;
      assert s1.Peek(6) == 0x899;
      assert s1.Peek(10) == 0xa16;
      assert s1.Peek(15) == 0x332;
      assert s1.Peek(21) == 0x13c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x13ad);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1348);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s473(s7, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 292
    * Starting at 0x1348
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x13ad

    requires s0.stack[4] == 0x13cf

    requires s0.stack[7] == 0x899

    requires s0.stack[11] == 0xa16

    requires s0.stack[16] == 0x332

    requires s0.stack[22] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13ad;
      assert s1.Peek(4) == 0x13cf;
      assert s1.Peek(7) == 0x899;
      assert s1.Peek(11) == 0xa16;
      assert s1.Peek(16) == 0x332;
      assert s1.Peek(22) == 0x13c;
      var s2 := Push32(s1, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x13ad;
      assert s11.Peek(4) == 0x13cf;
      assert s11.Peek(7) == 0x899;
      assert s11.Peek(11) == 0xa16;
      assert s11.Peek(16) == 0x332;
      assert s11.Peek(22) == 0x13c;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s474(s13, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 295
    * Starting at 0x13ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x13cf

    requires s0.stack[5] == 0x899

    requires s0.stack[9] == 0xa16

    requires s0.stack[14] == 0x332

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13cf;
      assert s1.Peek(5) == 0x899;
      assert s1.Peek(9) == 0xa16;
      assert s1.Peek(14) == 0x332;
      assert s1.Peek(20) == 0x13c;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s475(s10, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 297
    * Starting at 0x13cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x899

    requires s0.stack[7] == 0xa16

    requires s0.stack[12] == 0x332

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x899;
      assert s1.Peek(7) == 0xa16;
      assert s1.Peek(12) == 0x332;
      assert s1.Peek(18) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s7, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 115
    * Starting at 0x899
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x899 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xa16

    requires s0.stack[9] == 0x332

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa16;
      assert s1.Peek(9) == 0x332;
      assert s1.Peek(15) == 0x13c;
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

  /** Node 477
    * Segment Id for this node is: 116
    * Starting at 0x8a2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xa16

    requires s0.stack[8] == 0x332

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa16;
      assert s1.Peek(8) == 0x332;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0xa16;
      assert s11.Peek(11) == 0x332;
      assert s11.Peek(17) == 0x13c;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(6) == 0xa16;
      assert s21.Peek(11) == 0x332;
      assert s21.Peek(17) == 0x13c;
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
      assert s31.Peek(6) == 0xa16;
      assert s31.Peek(11) == 0x332;
      assert s31.Peek(17) == 0x13c;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s478(s41, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 117
    * Starting at 0x920
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x920 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xa16

    requires s0.stack[8] == 0x332

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0xa16;
      assert s1.Peek(9) == 0x332;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x097c);
      assert s11.Peek(0) == 0x97c;
      assert s11.Peek(9) == 0xa16;
      assert s11.Peek(14) == 0x332;
      assert s11.Peek(20) == 0x13c;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0eb7);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s479(s15, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 186
    * Starting at 0xeb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x97c

    requires s0.stack[9] == 0xa16

    requires s0.stack[14] == 0x332

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x97c;
      assert s1.Peek(9) == 0xa16;
      assert s1.Peek(14) == 0x332;
      assert s1.Peek(20) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0eca);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xeca;
      assert s11.Peek(5) == 0x97c;
      assert s11.Peek(12) == 0xa16;
      assert s11.Peek(17) == 0x332;
      assert s11.Peek(23) == 0x13c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0ea8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s480(s14, gas - 1)
  }

  /** Node 480
    * Segment Id for this node is: 184
    * Starting at 0xea8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[2] == 0xeca

    requires s0.stack[6] == 0x97c

    requires s0.stack[13] == 0xa16

    requires s0.stack[18] == 0x332

    requires s0.stack[24] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeca;
      assert s1.Peek(6) == 0x97c;
      assert s1.Peek(13) == 0xa16;
      assert s1.Peek(18) == 0x332;
      assert s1.Peek(24) == 0x13c;
      var s2 := Push2(s1, 0x0eb1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s481(s5, gas - 1)
  }

  /** Node 481
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xeb1

    requires s0.stack[4] == 0xeca

    requires s0.stack[8] == 0x97c

    requires s0.stack[15] == 0xa16

    requires s0.stack[20] == 0x332

    requires s0.stack[26] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb1;
      assert s1.Peek(4) == 0xeca;
      assert s1.Peek(8) == 0x97c;
      assert s1.Peek(15) == 0xa16;
      assert s1.Peek(20) == 0x332;
      assert s1.Peek(26) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s9, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 185
    * Starting at 0xeb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0xeca

    requires s0.stack[7] == 0x97c

    requires s0.stack[14] == 0xa16

    requires s0.stack[19] == 0x332

    requires s0.stack[25] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xeca;
      assert s1.Peek(7) == 0x97c;
      assert s1.Peek(14) == 0xa16;
      assert s1.Peek(19) == 0x332;
      assert s1.Peek(25) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s483(s6, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 187
    * Starting at 0xeca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0x97c

    requires s0.stack[10] == 0xa16

    requires s0.stack[15] == 0x332

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x97c;
      assert s1.Peek(10) == 0xa16;
      assert s1.Peek(15) == 0x332;
      assert s1.Peek(21) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s484(s6, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 118
    * Starting at 0x97c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0xa16

    requires s0.stack[12] == 0x332

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xa16;
      assert s1.Peek(12) == 0x332;
      assert s1.Peek(18) == 0x13c;
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
      assert s11.Peek(0) == 0xa16;
      assert s11.Peek(5) == 0x332;
      assert s11.Peek(11) == 0x13c;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s12, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 126
    * Starting at 0xa16
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x332

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s486(s1, gas - 1)
  }

  /** Node 486
    * Segment Id for this node is: 127
    * Starting at 0xa17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x332

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x332;
      assert s1.Peek(10) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s487(s6, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 72
    * Starting at 0x332
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x332 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x13c;
      var s2 := Push2(s1, 0x033d);
      var s3 := Dup6(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Push2(s5, 0x0a1d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s488(s7, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 128
    * Starting at 0xa1d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x33d

    requires s0.stack[9] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33d;
      assert s1.Peek(9) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x04);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x33d;
      assert s11.Peek(12) == 0x13c;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x33d;
      assert s21.Peek(11) == 0x13c;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0aa1);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s498(s29, gas - 1)
      else
        ExecuteFromCFGNode_s489(s29, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 129
    * Starting at 0xa67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x33d

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x33d;
      assert s1.Peek(11) == 0x13c;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a98);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x14e1);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s490(s11, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 314
    * Starting at 0x14e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xa98

    requires s0.stack[6] == 0x33d

    requires s0.stack[12] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa98;
      assert s1.Peek(6) == 0x33d;
      assert s1.Peek(12) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0xa98;
      assert s11.Peek(9) == 0x33d;
      assert s11.Peek(15) == 0x13c;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x14f8);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x14bf);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s18, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 311
    * Starting at 0x14bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x14f8

    requires s0.stack[4] == 0xa98

    requires s0.stack[9] == 0x33d

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x14f8;
      assert s1.Peek(4) == 0xa98;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x14cb);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s492(s7, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x14cb

    requires s0.stack[5] == 0x14f8

    requires s0.stack[8] == 0xa98

    requires s0.stack[13] == 0x33d

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14cb;
      assert s1.Peek(5) == 0x14f8;
      assert s1.Peek(8) == 0xa98;
      assert s1.Peek(13) == 0x33d;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x14cb;
      assert s11.Peek(6) == 0x14f8;
      assert s11.Peek(9) == 0xa98;
      assert s11.Peek(14) == 0x33d;
      assert s11.Peek(20) == 0x13c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s493(s15, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 312
    * Starting at 0x14cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x14f8

    requires s0.stack[6] == 0xa98

    requires s0.stack[11] == 0x33d

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x14f8;
      assert s1.Peek(6) == 0xa98;
      assert s1.Peek(11) == 0x33d;
      assert s1.Peek(17) == 0x13c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x14d6);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1471);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s494(s7, gas - 1)
  }

  /** Node 494
    * Segment Id for this node is: 310
    * Starting at 0x1471
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1471 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x14d6

    requires s0.stack[4] == 0x14f8

    requires s0.stack[7] == 0xa98

    requires s0.stack[12] == 0x33d

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x14d6;
      assert s1.Peek(4) == 0x14f8;
      assert s1.Peek(7) == 0xa98;
      assert s1.Peek(12) == 0x33d;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x616c616e63650000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x14d6;
      assert s11.Peek(4) == 0x14f8;
      assert s11.Peek(7) == 0xa98;
      assert s11.Peek(12) == 0x33d;
      assert s11.Peek(18) == 0x13c;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s495(s13, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 313
    * Starting at 0x14d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x14f8

    requires s0.stack[5] == 0xa98

    requires s0.stack[10] == 0x33d

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14f8;
      assert s1.Peek(5) == 0xa98;
      assert s1.Peek(10) == 0x33d;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s496(s10, gas - 1)
  }

  /** Node 496
    * Segment Id for this node is: 315
    * Starting at 0x14f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xa98

    requires s0.stack[8] == 0x33d

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa98;
      assert s1.Peek(8) == 0x33d;
      assert s1.Peek(14) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s497(s7, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 130
    * Starting at 0xa98
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x33d

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x33d;
      assert s1.Peek(11) == 0x13c;
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

  /** Node 498
    * Segment Id for this node is: 131
    * Starting at 0xaa1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x33d

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x33d;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0b0f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s508(s10, gas - 1)
      else
        ExecuteFromCFGNode_s499(s10, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 132
    * Starting at 0xad5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x33d

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x33d;
      assert s1.Peek(11) == 0x13c;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0b06);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x156f);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s11, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 320
    * Starting at 0x156f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x156f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xb06

    requires s0.stack[6] == 0x33d

    requires s0.stack[12] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb06;
      assert s1.Peek(6) == 0x33d;
      assert s1.Peek(12) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0xb06;
      assert s11.Peek(9) == 0x33d;
      assert s11.Peek(15) == 0x13c;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1586);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x154d);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s501(s18, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 317
    * Starting at 0x154d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x1586

    requires s0.stack[4] == 0xb06

    requires s0.stack[9] == 0x33d

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1586;
      assert s1.Peek(4) == 0xb06;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1559);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s502(s7, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x1559

    requires s0.stack[5] == 0x1586

    requires s0.stack[8] == 0xb06

    requires s0.stack[13] == 0x33d

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1559;
      assert s1.Peek(5) == 0x1586;
      assert s1.Peek(8) == 0xb06;
      assert s1.Peek(13) == 0x33d;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1559;
      assert s11.Peek(6) == 0x1586;
      assert s11.Peek(9) == 0xb06;
      assert s11.Peek(14) == 0x33d;
      assert s11.Peek(20) == 0x13c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s503(s15, gas - 1)
  }

  /** Node 503
    * Segment Id for this node is: 318
    * Starting at 0x1559
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1559 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x1586

    requires s0.stack[6] == 0xb06

    requires s0.stack[11] == 0x33d

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1586;
      assert s1.Peek(6) == 0xb06;
      assert s1.Peek(11) == 0x33d;
      assert s1.Peek(17) == 0x13c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1564);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x14ff);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s504(s7, gas - 1)
  }

  /** Node 504
    * Segment Id for this node is: 316
    * Starting at 0x14ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x1564

    requires s0.stack[4] == 0x1586

    requires s0.stack[7] == 0xb06

    requires s0.stack[12] == 0x33d

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1564;
      assert s1.Peek(4) == 0x1586;
      assert s1.Peek(7) == 0xb06;
      assert s1.Peek(12) == 0x33d;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push32(s1, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6472657373000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x1564;
      assert s11.Peek(4) == 0x1586;
      assert s11.Peek(7) == 0xb06;
      assert s11.Peek(12) == 0x33d;
      assert s11.Peek(18) == 0x13c;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s505(s13, gas - 1)
  }

  /** Node 505
    * Segment Id for this node is: 319
    * Starting at 0x1564
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1564 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x1586

    requires s0.stack[5] == 0xb06

    requires s0.stack[10] == 0x33d

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1586;
      assert s1.Peek(5) == 0xb06;
      assert s1.Peek(10) == 0x33d;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s506(s10, gas - 1)
  }

  /** Node 506
    * Segment Id for this node is: 321
    * Starting at 0x1586
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1586 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xb06

    requires s0.stack[8] == 0x33d

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb06;
      assert s1.Peek(8) == 0x33d;
      assert s1.Peek(14) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s507(s7, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 133
    * Starting at 0xb06
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x33d

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x33d;
      assert s1.Peek(11) == 0x13c;
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

  /** Node 508
    * Segment Id for this node is: 134
    * Starting at 0xb0f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x33d

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x33d;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0b7d);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s518(s10, gas - 1)
      else
        ExecuteFromCFGNode_s509(s10, gas - 1)
  }

  /** Node 509
    * Segment Id for this node is: 135
    * Starting at 0xb43
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x33d

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x33d;
      assert s1.Peek(11) == 0x13c;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0b74);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x15fd);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s510(s11, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 326
    * Starting at 0x15fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xb74

    requires s0.stack[6] == 0x33d

    requires s0.stack[12] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb74;
      assert s1.Peek(6) == 0x33d;
      assert s1.Peek(12) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0xb74;
      assert s11.Peek(9) == 0x33d;
      assert s11.Peek(15) == 0x13c;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1614);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x15db);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s511(s18, gas - 1)
  }

  /** Node 511
    * Segment Id for this node is: 323
    * Starting at 0x15db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x1614

    requires s0.stack[4] == 0xb74

    requires s0.stack[9] == 0x33d

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1614;
      assert s1.Peek(4) == 0xb74;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x15e7);
      var s4 := Push1(s3, 0x23);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s512(s7, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x15e7

    requires s0.stack[5] == 0x1614

    requires s0.stack[8] == 0xb74

    requires s0.stack[13] == 0x33d

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15e7;
      assert s1.Peek(5) == 0x1614;
      assert s1.Peek(8) == 0xb74;
      assert s1.Peek(13) == 0x33d;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x15e7;
      assert s11.Peek(6) == 0x1614;
      assert s11.Peek(9) == 0xb74;
      assert s11.Peek(14) == 0x33d;
      assert s11.Peek(20) == 0x13c;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s15, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 324
    * Starting at 0x15e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x1614

    requires s0.stack[6] == 0xb74

    requires s0.stack[11] == 0x33d

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1614;
      assert s1.Peek(6) == 0xb74;
      assert s1.Peek(11) == 0x33d;
      assert s1.Peek(17) == 0x13c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x15f2);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x158d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s514(s7, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 322
    * Starting at 0x158d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x158d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x15f2

    requires s0.stack[4] == 0x1614

    requires s0.stack[7] == 0xb74

    requires s0.stack[12] == 0x33d

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x15f2;
      assert s1.Peek(4) == 0x1614;
      assert s1.Peek(7) == 0xb74;
      assert s1.Peek(12) == 0x33d;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6573730000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x15f2;
      assert s11.Peek(4) == 0x1614;
      assert s11.Peek(7) == 0xb74;
      assert s11.Peek(12) == 0x33d;
      assert s11.Peek(18) == 0x13c;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s515(s13, gas - 1)
  }

  /** Node 515
    * Segment Id for this node is: 325
    * Starting at 0x15f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x1614

    requires s0.stack[5] == 0xb74

    requires s0.stack[10] == 0x33d

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1614;
      assert s1.Peek(5) == 0xb74;
      assert s1.Peek(10) == 0x33d;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s516(s10, gas - 1)
  }

  /** Node 516
    * Segment Id for this node is: 327
    * Starting at 0x1614
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1614 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xb74

    requires s0.stack[8] == 0x33d

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb74;
      assert s1.Peek(8) == 0x33d;
      assert s1.Peek(14) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s517(s7, gas - 1)
  }

  /** Node 517
    * Segment Id for this node is: 136
    * Starting at 0xb74
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x33d

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x33d;
      assert s1.Peek(11) == 0x13c;
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

  /** Node 518
    * Segment Id for this node is: 137
    * Starting at 0xb7d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x33d

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x33d;
      assert s1.Peek(10) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x04);
      var s4 := Push0(s3);
      var s5 := Dup7(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x33d;
      assert s11.Peek(13) == 0x13c;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(6) == 0x33d;
      assert s21.Peek(12) == 0x13c;
      var s22 := Push2(s21, 0x0bc6);
      var s23 := Swap2(s22);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x143e);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s519(s26, gas - 1)
  }

  /** Node 519
    * Segment Id for this node is: 304
    * Starting at 0x143e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xbc6

    requires s0.stack[7] == 0x33d

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbc6;
      assert s1.Peek(7) == 0x33d;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1448);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0e04);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s520(s6, gas - 1)
  }

  /** Node 520
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1448

    requires s0.stack[5] == 0xbc6

    requires s0.stack[10] == 0x33d

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1448;
      assert s1.Peek(5) == 0xbc6;
      assert s1.Peek(10) == 0x33d;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s521(s9, gas - 1)
  }

  /** Node 521
    * Segment Id for this node is: 305
    * Starting at 0x1448
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1448 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xbc6

    requires s0.stack[9] == 0x33d

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbc6;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1453);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e04);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s522(s7, gas - 1)
  }

  /** Node 522
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1453

    requires s0.stack[5] == 0xbc6

    requires s0.stack[10] == 0x33d

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1453;
      assert s1.Peek(5) == 0xbc6;
      assert s1.Peek(10) == 0x33d;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s523(s9, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 306
    * Starting at 0x1453
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1453 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xbc6

    requires s0.stack[9] == 0x33d

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbc6;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup2(s8);
      var s10 := Dup2(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xbc6;
      assert s11.Peek(9) == 0x33d;
      assert s11.Peek(15) == 0x13c;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x146b);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s526(s14, gas - 1)
      else
        ExecuteFromCFGNode_s524(s14, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 307
    * Starting at 0x1463
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xbc6

    requires s0.stack[8] == 0x33d

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x146a);
      assert s1.Peek(0) == 0x146a;
      assert s1.Peek(4) == 0xbc6;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s525(s3, gas - 1)
  }

  /** Node 525
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x146a

    requires s0.stack[4] == 0xbc6

    requires s0.stack[9] == 0x33d

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x146a;
      assert s1.Peek(4) == 0xbc6;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 526
    * Segment Id for this node is: 309
    * Starting at 0x146b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xbc6

    requires s0.stack[8] == 0x33d

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbc6;
      assert s1.Peek(8) == 0x33d;
      assert s1.Peek(14) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s527(s6, gas - 1)
  }

  /** Node 527
    * Segment Id for this node is: 138
    * Starting at 0xbc6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x33d

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x33d;
      assert s1.Peek(11) == 0x13c;
      var s2 := Push1(s1, 0x04);
      var s3 := Push0(s2);
      var s4 := Dup7(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(8) == 0x33d;
      assert s11.Peek(14) == 0x13c;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push0(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(7) == 0x33d;
      assert s21.Peek(13) == 0x13c;
      var s22 := SStore(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Push1(s24, 0x04);
      var s26 := Push0(s25);
      var s27 := Dup6(s26);
      var s28 := Push20(s27, 0xffffffffffffffffffffffffffffffffffffffff);
      var s29 := And(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(8) == 0x33d;
      assert s31.Peek(14) == 0x13c;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Swap1(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x20);
      var s40 := Add(s39);
      var s41 := Push0(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s528(s41, gas - 1)
  }

  /** Node 528
    * Segment Id for this node is: 139
    * Starting at 0xc45
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc45 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x33d

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Keccak256(s0);
      assert s1.Peek(6) == 0x33d;
      assert s1.Peek(12) == 0x13c;
      var s2 := SLoad(s1);
      var s3 := Push2(s2, 0x0c50);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x161b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s529(s7, gas - 1)
  }

  /** Node 529
    * Segment Id for this node is: 328
    * Starting at 0x161b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x161b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xc50

    requires s0.stack[7] == 0x33d

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc50;
      assert s1.Peek(7) == 0x33d;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1625);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0e04);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s530(s6, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1625

    requires s0.stack[5] == 0xc50

    requires s0.stack[10] == 0x33d

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1625;
      assert s1.Peek(5) == 0xc50;
      assert s1.Peek(10) == 0x33d;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s531(s9, gas - 1)
  }

  /** Node 531
    * Segment Id for this node is: 329
    * Starting at 0x1625
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1625 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xc50

    requires s0.stack[9] == 0x33d

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc50;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1630);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e04);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s532(s7, gas - 1)
  }

  /** Node 532
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1630

    requires s0.stack[5] == 0xc50

    requires s0.stack[10] == 0x33d

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1630;
      assert s1.Peek(5) == 0xc50;
      assert s1.Peek(10) == 0x33d;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s533(s9, gas - 1)
  }

  /** Node 533
    * Segment Id for this node is: 330
    * Starting at 0x1630
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1630 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xc50

    requires s0.stack[9] == 0x33d

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc50;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xc50;
      assert s11.Peek(9) == 0x33d;
      assert s11.Peek(15) == 0x13c;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1648);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s536(s14, gas - 1)
      else
        ExecuteFromCFGNode_s534(s14, gas - 1)
  }

  /** Node 534
    * Segment Id for this node is: 331
    * Starting at 0x1640
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1640 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xc50

    requires s0.stack[8] == 0x33d

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1647);
      assert s1.Peek(0) == 0x1647;
      assert s1.Peek(4) == 0xc50;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push2(s1, 0x10d3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s535(s3, gas - 1)
  }

  /** Node 535
    * Segment Id for this node is: 237
    * Starting at 0x10d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x1647

    requires s0.stack[4] == 0xc50

    requires s0.stack[9] == 0x33d

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1647;
      assert s1.Peek(4) == 0xc50;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 536
    * Segment Id for this node is: 333
    * Starting at 0x1648
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1648 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xc50

    requires s0.stack[8] == 0x33d

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc50;
      assert s1.Peek(8) == 0x33d;
      assert s1.Peek(14) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s537(s6, gas - 1)
  }

  /** Node 537
    * Segment Id for this node is: 140
    * Starting at 0xc50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x33d

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x33d;
      assert s1.Peek(11) == 0x13c;
      var s2 := Push1(s1, 0x04);
      var s3 := Push0(s2);
      var s4 := Dup6(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(8) == 0x33d;
      assert s11.Peek(14) == 0x13c;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push0(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(7) == 0x33d;
      assert s21.Peek(13) == 0x13c;
      var s22 := SStore(s21);
      var s23 := Pop(s22);
      var s24 := Dup3(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup5(s26);
      var s28 := Push20(s27, 0xffffffffffffffffffffffffffffffffffffffff);
      var s29 := And(s28);
      var s30 := Push32(s29, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s31 := Dup5(s30);
      assert s31.Peek(8) == 0x33d;
      assert s31.Peek(14) == 0x13c;
      var s32 := Push1(s31, 0x40);
      var s33 := MLoad(s32);
      var s34 := Push2(s33, 0x0cee);
      var s35 := Swap2(s34);
      var s36 := Swap1(s35);
      var s37 := Push2(s36, 0x0eb7);
      var s38 := Jump(s37);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s538(s38, gas - 1)
  }

  /** Node 538
    * Segment Id for this node is: 186
    * Starting at 0xeb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xcee

    requires s0.stack[10] == 0x33d

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcee;
      assert s1.Peek(10) == 0x33d;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0eca);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xeca;
      assert s11.Peek(5) == 0xcee;
      assert s11.Peek(13) == 0x33d;
      assert s11.Peek(19) == 0x13c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0ea8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s539(s14, gas - 1)
  }

  /** Node 539
    * Segment Id for this node is: 184
    * Starting at 0xea8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xeca

    requires s0.stack[6] == 0xcee

    requires s0.stack[14] == 0x33d

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeca;
      assert s1.Peek(6) == 0xcee;
      assert s1.Peek(14) == 0x33d;
      assert s1.Peek(20) == 0x13c;
      var s2 := Push2(s1, 0x0eb1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s540(s5, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0xeb1

    requires s0.stack[4] == 0xeca

    requires s0.stack[8] == 0xcee

    requires s0.stack[16] == 0x33d

    requires s0.stack[22] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb1;
      assert s1.Peek(4) == 0xeca;
      assert s1.Peek(8) == 0xcee;
      assert s1.Peek(16) == 0x33d;
      assert s1.Peek(22) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s541(s9, gas - 1)
  }

  /** Node 541
    * Segment Id for this node is: 185
    * Starting at 0xeb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xeca

    requires s0.stack[7] == 0xcee

    requires s0.stack[15] == 0x33d

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xeca;
      assert s1.Peek(7) == 0xcee;
      assert s1.Peek(15) == 0x33d;
      assert s1.Peek(21) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s6, gas - 1)
  }

  /** Node 542
    * Segment Id for this node is: 187
    * Starting at 0xeca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xcee

    requires s0.stack[11] == 0x33d

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcee;
      assert s1.Peek(11) == 0x33d;
      assert s1.Peek(17) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s543(s6, gas - 1)
  }

  /** Node 543
    * Segment Id for this node is: 141
    * Starting at 0xcee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x33d

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x33d;
      assert s1.Peek(14) == 0x13c;
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
      assert s11.Peek(1) == 0x33d;
      assert s11.Peek(7) == 0x13c;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s544(s13, gas - 1)
  }

  /** Node 544
    * Segment Id for this node is: 73
    * Starting at 0x33d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x13c;
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
      ExecuteFromCFGNode_s545(s11, gas - 1)
  }

  /** Node 545
    * Segment Id for this node is: 30
    * Starting at 0x13c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0149);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0e8f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s546(s8, gas - 1)
  }

  /** Node 546
    * Segment Id for this node is: 182
    * Starting at 0xe8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x149

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x149;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0ea2);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xea2;
      assert s11.Peek(5) == 0x149;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e80);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s547(s14, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 180
    * Starting at 0xe80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xea2

    requires s0.stack[6] == 0x149

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xea2;
      assert s1.Peek(6) == 0x149;
      var s2 := Push2(s1, 0x0e89);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s548(s5, gas - 1)
  }

  /** Node 548
    * Segment Id for this node is: 179
    * Starting at 0xe75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe89

    requires s0.stack[4] == 0xea2

    requires s0.stack[8] == 0x149

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe89;
      assert s1.Peek(4) == 0xea2;
      assert s1.Peek(8) == 0x149;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s549(s11, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 181
    * Starting at 0xe89
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xea2

    requires s0.stack[7] == 0x149

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xea2;
      assert s1.Peek(7) == 0x149;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s550(s6, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 183
    * Starting at 0xea2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x149

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x149;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s551(s6, gas - 1)
  }

  /** Node 551
    * Segment Id for this node is: 31
    * Starting at 0x149
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x149 as nat
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

  /** Node 552
    * Segment Id for this node is: 25
    * Starting at 0x104
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x010c);
      var s3 := Push2(s2, 0x031a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s553(s4, gas - 1)
  }

  /** Node 553
    * Segment Id for this node is: 70
    * Starting at 0x31a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x10c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s554(s8, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 26
    * Starting at 0x10c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0119);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0eb7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s555(s8, gas - 1)
  }

  /** Node 555
    * Segment Id for this node is: 186
    * Starting at 0xeb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x119;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0eca);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xeca;
      assert s11.Peek(5) == 0x119;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0ea8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s556(s14, gas - 1)
  }

  /** Node 556
    * Segment Id for this node is: 184
    * Starting at 0xea8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xeca

    requires s0.stack[6] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeca;
      assert s1.Peek(6) == 0x119;
      var s2 := Push2(s1, 0x0eb1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s557(s5, gas - 1)
  }

  /** Node 557
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s557(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xeb1

    requires s0.stack[4] == 0xeca

    requires s0.stack[8] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb1;
      assert s1.Peek(4) == 0xeca;
      assert s1.Peek(8) == 0x119;
      var s2 := Push0(s1);
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
    * Segment Id for this node is: 185
    * Starting at 0xeb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s558(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xeca

    requires s0.stack[7] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xeca;
      assert s1.Peek(7) == 0x119;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s559(s6, gas - 1)
  }

  /** Node 559
    * Segment Id for this node is: 187
    * Starting at 0xeca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s559(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x119;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s560(s6, gas - 1)
  }

  /** Node 560
    * Segment Id for this node is: 27
    * Starting at 0x119
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s560(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x119 as nat
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

  /** Node 561
    * Segment Id for this node is: 21
    * Starting at 0xd4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s561(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00ee);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x00e9);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0xe9;
      assert s11.Peek(3) == 0xee;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0e37);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s562(s14, gas - 1)
  }

  /** Node 562
    * Segment Id for this node is: 173
    * Starting at 0xe37
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s562(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xe9

    requires s0.stack[3] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe9;
      assert s1.Peek(3) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0e4d);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s565(s11, gas - 1)
      else
        ExecuteFromCFGNode_s563(s11, gas - 1)
  }

  /** Node 563
    * Segment Id for this node is: 174
    * Starting at 0xe45
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s563(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe45 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xe9

    requires s0.stack[5] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e4c);
      assert s1.Peek(0) == 0xe4c;
      assert s1.Peek(5) == 0xe9;
      assert s1.Peek(6) == 0xee;
      var s2 := Push2(s1, 0x0da6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s564(s3, gas - 1)
  }

  /** Node 564
    * Segment Id for this node is: 156
    * Starting at 0xda6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s564(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xe4c

    requires s0.stack[5] == 0xe9

    requires s0.stack[6] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe4c;
      assert s1.Peek(5) == 0xe9;
      assert s1.Peek(6) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 565
    * Segment Id for this node is: 176
    * Starting at 0xe4d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s565(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xe9

    requires s0.stack[5] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe9;
      assert s1.Peek(5) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0e5a);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0df0);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s566(s9, gas - 1)
  }

  /** Node 566
    * Segment Id for this node is: 164
    * Starting at 0xdf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s566(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe5a

    requires s0.stack[8] == 0xe9

    requires s0.stack[9] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe5a;
      assert s1.Peek(8) == 0xe9;
      assert s1.Peek(9) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0dfe);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s567(s10, gas - 1)
  }

  /** Node 567
    * Segment Id for this node is: 160
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s567(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xe5a

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xe5a;
      assert s1.Peek(11) == 0xe9;
      assert s1.Peek(12) == 0xee;
      var s2 := Push2(s1, 0x0de3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dc9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s568(s5, gas - 1)
  }

  /** Node 568
    * Segment Id for this node is: 158
    * Starting at 0xdc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s568(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xde3

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0xe5a

    requires s0.stack[13] == 0xe9

    requires s0.stack[14] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde3;
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0xe5a;
      assert s1.Peek(13) == 0xe9;
      assert s1.Peek(14) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0dd3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0daa);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s569(s6, gas - 1)
  }

  /** Node 569
    * Segment Id for this node is: 157
    * Starting at 0xdaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s569(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xdd3

    requires s0.stack[4] == 0xde3

    requires s0.stack[6] == 0xdfe

    requires s0.stack[10] == 0xe5a

    requires s0.stack[16] == 0xe9

    requires s0.stack[17] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdd3;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(6) == 0xdfe;
      assert s1.Peek(10) == 0xe5a;
      assert s1.Peek(16) == 0xe9;
      assert s1.Peek(17) == 0xee;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s570(s11, gas - 1)
  }

  /** Node 570
    * Segment Id for this node is: 159
    * Starting at 0xdd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s570(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xde3

    requires s0.stack[5] == 0xdfe

    requires s0.stack[9] == 0xe5a

    requires s0.stack[15] == 0xe9

    requires s0.stack[16] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(5) == 0xdfe;
      assert s1.Peek(9) == 0xe5a;
      assert s1.Peek(15) == 0xe9;
      assert s1.Peek(16) == 0xee;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s571(s7, gas - 1)
  }

  /** Node 571
    * Segment Id for this node is: 161
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s571(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0xe5a

    requires s0.stack[12] == 0xe9

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xe5a;
      assert s1.Peek(12) == 0xe9;
      assert s1.Peek(13) == 0xee;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ded);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s573(s5, gas - 1)
      else
        ExecuteFromCFGNode_s572(s5, gas - 1)
  }

  /** Node 572
    * Segment Id for this node is: 162
    * Starting at 0xdea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s572(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xe5a

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xe5a;
      assert s1.Peek(12) == 0xe9;
      assert s1.Peek(13) == 0xee;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 573
    * Segment Id for this node is: 163
    * Starting at 0xded
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s573(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xdfe

    requires s0.stack[5] == 0xe5a

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdfe;
      assert s1.Peek(5) == 0xe5a;
      assert s1.Peek(11) == 0xe9;
      assert s1.Peek(12) == 0xee;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s574(s3, gas - 1)
  }

  /** Node 574
    * Segment Id for this node is: 165
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s574(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe5a

    requires s0.stack[9] == 0xe9

    requires s0.stack[10] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe5a;
      assert s1.Peek(9) == 0xe9;
      assert s1.Peek(10) == 0xee;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s575(s6, gas - 1)
  }

  /** Node 575
    * Segment Id for this node is: 177
    * Starting at 0xe5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s575(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xe9

    requires s0.stack[7] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xe9;
      assert s1.Peek(7) == 0xee;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0e6b);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0e23);
      assert s11.Peek(0) == 0xe23;
      assert s11.Peek(3) == 0xe6b;
      assert s11.Peek(9) == 0xe9;
      assert s11.Peek(10) == 0xee;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s576(s12, gas - 1)
  }

  /** Node 576
    * Segment Id for this node is: 171
    * Starting at 0xe23
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s576(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe6b

    requires s0.stack[8] == 0xe9

    requires s0.stack[9] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe6b;
      assert s1.Peek(8) == 0xe9;
      assert s1.Peek(9) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0e31);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0e0d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s577(s10, gas - 1)
  }

  /** Node 577
    * Segment Id for this node is: 167
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s577(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0xe6b

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe31;
      assert s1.Peek(5) == 0xe6b;
      assert s1.Peek(11) == 0xe9;
      assert s1.Peek(12) == 0xee;
      var s2 := Push2(s1, 0x0e16);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s578(s5, gas - 1)
  }

  /** Node 578
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s578(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xe16

    requires s0.stack[3] == 0xe31

    requires s0.stack[7] == 0xe6b

    requires s0.stack[13] == 0xe9

    requires s0.stack[14] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe16;
      assert s1.Peek(3) == 0xe31;
      assert s1.Peek(7) == 0xe6b;
      assert s1.Peek(13) == 0xe9;
      assert s1.Peek(14) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s579(s9, gas - 1)
  }

  /** Node 579
    * Segment Id for this node is: 168
    * Starting at 0xe16
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s579(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xe31

    requires s0.stack[6] == 0xe6b

    requires s0.stack[12] == 0xe9

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe31;
      assert s1.Peek(6) == 0xe6b;
      assert s1.Peek(12) == 0xe9;
      assert s1.Peek(13) == 0xee;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0e20);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s581(s5, gas - 1)
      else
        ExecuteFromCFGNode_s580(s5, gas - 1)
  }

  /** Node 580
    * Segment Id for this node is: 169
    * Starting at 0xe1d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s580(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0xe6b

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xe31;
      assert s1.Peek(6) == 0xe6b;
      assert s1.Peek(12) == 0xe9;
      assert s1.Peek(13) == 0xee;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 581
    * Segment Id for this node is: 170
    * Starting at 0xe20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s581(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xe31

    requires s0.stack[5] == 0xe6b

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe31;
      assert s1.Peek(5) == 0xe6b;
      assert s1.Peek(11) == 0xe9;
      assert s1.Peek(12) == 0xee;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s582(s3, gas - 1)
  }

  /** Node 582
    * Segment Id for this node is: 172
    * Starting at 0xe31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s582(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe6b

    requires s0.stack[9] == 0xe9

    requires s0.stack[10] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe6b;
      assert s1.Peek(9) == 0xe9;
      assert s1.Peek(10) == 0xee;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s583(s6, gas - 1)
  }

  /** Node 583
    * Segment Id for this node is: 178
    * Starting at 0xe6b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s583(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xe9

    requires s0.stack[7] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xe9;
      assert s1.Peek(7) == 0xee;
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
      ExecuteFromCFGNode_s584(s10, gas - 1)
  }

  /** Node 584
    * Segment Id for this node is: 22
    * Starting at 0xe9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s584(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xee;
      var s2 := Push2(s1, 0x0304);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s585(s3, gas - 1)
  }

  /** Node 585
    * Segment Id for this node is: 68
    * Starting at 0x304
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s585(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0310);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x07c6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s586(s8, gas - 1)
  }

  /** Node 586
    * Segment Id for this node is: 110
    * Starting at 0x7c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s586(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x310

    requires s0.stack[7] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x310;
      assert s1.Peek(7) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0834);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s596(s10, gas - 1)
      else
        ExecuteFromCFGNode_s587(s10, gas - 1)
  }

  /** Node 587
    * Segment Id for this node is: 111
    * Starting at 0x7fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s587(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x310

    requires s0.stack[7] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x310;
      assert s1.Peek(8) == 0xee;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x082b);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x132a);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s588(s11, gas - 1)
  }

  /** Node 588
    * Segment Id for this node is: 290
    * Starting at 0x132a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s588(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x82b

    requires s0.stack[5] == 0x310

    requires s0.stack[9] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x82b;
      assert s1.Peek(5) == 0x310;
      assert s1.Peek(9) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x82b;
      assert s11.Peek(8) == 0x310;
      assert s11.Peek(12) == 0xee;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1341);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1308);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s589(s18, gas - 1)
  }

  /** Node 589
    * Segment Id for this node is: 287
    * Starting at 0x1308
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s589(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1308 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x1341

    requires s0.stack[4] == 0x82b

    requires s0.stack[8] == 0x310

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1341;
      assert s1.Peek(4) == 0x82b;
      assert s1.Peek(8) == 0x310;
      assert s1.Peek(12) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1314);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s590(s7, gas - 1)
  }

  /** Node 590
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s590(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x1314

    requires s0.stack[5] == 0x1341

    requires s0.stack[8] == 0x82b

    requires s0.stack[12] == 0x310

    requires s0.stack[16] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1314;
      assert s1.Peek(5) == 0x1341;
      assert s1.Peek(8) == 0x82b;
      assert s1.Peek(12) == 0x310;
      assert s1.Peek(16) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1314;
      assert s11.Peek(6) == 0x1341;
      assert s11.Peek(9) == 0x82b;
      assert s11.Peek(13) == 0x310;
      assert s11.Peek(17) == 0xee;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s591(s15, gas - 1)
  }

  /** Node 591
    * Segment Id for this node is: 288
    * Starting at 0x1314
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s591(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1314 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x1341

    requires s0.stack[6] == 0x82b

    requires s0.stack[10] == 0x310

    requires s0.stack[14] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1341;
      assert s1.Peek(6) == 0x82b;
      assert s1.Peek(10) == 0x310;
      assert s1.Peek(14) == 0xee;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x131f);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x12ba);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s592(s7, gas - 1)
  }

  /** Node 592
    * Segment Id for this node is: 286
    * Starting at 0x12ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s592(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x131f

    requires s0.stack[4] == 0x1341

    requires s0.stack[7] == 0x82b

    requires s0.stack[11] == 0x310

    requires s0.stack[15] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x131f;
      assert s1.Peek(4) == 0x1341;
      assert s1.Peek(7) == 0x82b;
      assert s1.Peek(11) == 0x310;
      assert s1.Peek(15) == 0xee;
      var s2 := Push32(s1, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x131f;
      assert s11.Peek(4) == 0x1341;
      assert s11.Peek(7) == 0x82b;
      assert s11.Peek(11) == 0x310;
      assert s11.Peek(15) == 0xee;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s593(s13, gas - 1)
  }

  /** Node 593
    * Segment Id for this node is: 289
    * Starting at 0x131f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s593(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x1341

    requires s0.stack[5] == 0x82b

    requires s0.stack[9] == 0x310

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1341;
      assert s1.Peek(5) == 0x82b;
      assert s1.Peek(9) == 0x310;
      assert s1.Peek(13) == 0xee;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s594(s10, gas - 1)
  }

  /** Node 594
    * Segment Id for this node is: 291
    * Starting at 0x1341
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s594(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1341 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x82b

    requires s0.stack[7] == 0x310

    requires s0.stack[11] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x82b;
      assert s1.Peek(7) == 0x310;
      assert s1.Peek(11) == 0xee;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s595(s7, gas - 1)
  }

  /** Node 595
    * Segment Id for this node is: 112
    * Starting at 0x82b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s595(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x310

    requires s0.stack[8] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x310;
      assert s1.Peek(8) == 0xee;
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

  /** Node 596
    * Segment Id for this node is: 113
    * Starting at 0x834
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s596(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x834 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x310

    requires s0.stack[7] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x310;
      assert s1.Peek(7) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x08a2);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s606(s10, gas - 1)
      else
        ExecuteFromCFGNode_s597(s10, gas - 1)
  }

  /** Node 597
    * Segment Id for this node is: 114
    * Starting at 0x868
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s597(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x868 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x310

    requires s0.stack[7] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x310;
      assert s1.Peek(8) == 0xee;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0899);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x13b8);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s598(s11, gas - 1)
  }

  /** Node 598
    * Segment Id for this node is: 296
    * Starting at 0x13b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s598(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x899

    requires s0.stack[5] == 0x310

    requires s0.stack[9] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x899;
      assert s1.Peek(5) == 0x310;
      assert s1.Peek(9) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x899;
      assert s11.Peek(8) == 0x310;
      assert s11.Peek(12) == 0xee;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x13cf);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1396);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s599(s18, gas - 1)
  }

  /** Node 599
    * Segment Id for this node is: 293
    * Starting at 0x1396
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s599(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1396 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x13cf

    requires s0.stack[4] == 0x899

    requires s0.stack[8] == 0x310

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13cf;
      assert s1.Peek(4) == 0x899;
      assert s1.Peek(8) == 0x310;
      assert s1.Peek(12) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x13a2);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d06);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s600(s7, gas - 1)
  }

  /** Node 600
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s600(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x13a2

    requires s0.stack[5] == 0x13cf

    requires s0.stack[8] == 0x899

    requires s0.stack[12] == 0x310

    requires s0.stack[16] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13a2;
      assert s1.Peek(5) == 0x13cf;
      assert s1.Peek(8) == 0x899;
      assert s1.Peek(12) == 0x310;
      assert s1.Peek(16) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x13a2;
      assert s11.Peek(6) == 0x13cf;
      assert s11.Peek(9) == 0x899;
      assert s11.Peek(13) == 0x310;
      assert s11.Peek(17) == 0xee;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s601(s15, gas - 1)
  }

  /** Node 601
    * Segment Id for this node is: 294
    * Starting at 0x13a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s601(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x13cf

    requires s0.stack[6] == 0x899

    requires s0.stack[10] == 0x310

    requires s0.stack[14] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13cf;
      assert s1.Peek(6) == 0x899;
      assert s1.Peek(10) == 0x310;
      assert s1.Peek(14) == 0xee;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x13ad);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1348);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s602(s7, gas - 1)
  }

  /** Node 602
    * Segment Id for this node is: 292
    * Starting at 0x1348
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s602(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x13ad

    requires s0.stack[4] == 0x13cf

    requires s0.stack[7] == 0x899

    requires s0.stack[11] == 0x310

    requires s0.stack[15] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13ad;
      assert s1.Peek(4) == 0x13cf;
      assert s1.Peek(7) == 0x899;
      assert s1.Peek(11) == 0x310;
      assert s1.Peek(15) == 0xee;
      var s2 := Push32(s1, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x13ad;
      assert s11.Peek(4) == 0x13cf;
      assert s11.Peek(7) == 0x899;
      assert s11.Peek(11) == 0x310;
      assert s11.Peek(15) == 0xee;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s603(s13, gas - 1)
  }

  /** Node 603
    * Segment Id for this node is: 295
    * Starting at 0x13ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s603(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x13cf

    requires s0.stack[5] == 0x899

    requires s0.stack[9] == 0x310

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13cf;
      assert s1.Peek(5) == 0x899;
      assert s1.Peek(9) == 0x310;
      assert s1.Peek(13) == 0xee;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s604(s10, gas - 1)
  }

  /** Node 604
    * Segment Id for this node is: 297
    * Starting at 0x13cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s604(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x899

    requires s0.stack[7] == 0x310

    requires s0.stack[11] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x899;
      assert s1.Peek(7) == 0x310;
      assert s1.Peek(11) == 0xee;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s605(s7, gas - 1)
  }

  /** Node 605
    * Segment Id for this node is: 115
    * Starting at 0x899
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s605(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x899 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x310

    requires s0.stack[8] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x310;
      assert s1.Peek(8) == 0xee;
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

  /** Node 606
    * Segment Id for this node is: 116
    * Starting at 0x8a2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s606(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x310

    requires s0.stack[7] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x310;
      assert s1.Peek(7) == 0xee;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x310;
      assert s11.Peek(10) == 0xee;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(6) == 0x310;
      assert s21.Peek(10) == 0xee;
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
      assert s31.Peek(6) == 0x310;
      assert s31.Peek(10) == 0xee;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s607(s41, gas - 1)
  }

  /** Node 607
    * Segment Id for this node is: 117
    * Starting at 0x920
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s607(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x920 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x310

    requires s0.stack[7] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x310;
      assert s1.Peek(8) == 0xee;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x097c);
      assert s11.Peek(0) == 0x97c;
      assert s11.Peek(9) == 0x310;
      assert s11.Peek(13) == 0xee;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0eb7);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s608(s15, gas - 1)
  }

  /** Node 608
    * Segment Id for this node is: 186
    * Starting at 0xeb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s608(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x97c

    requires s0.stack[9] == 0x310

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x97c;
      assert s1.Peek(9) == 0x310;
      assert s1.Peek(13) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0eca);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xeca;
      assert s11.Peek(5) == 0x97c;
      assert s11.Peek(12) == 0x310;
      assert s11.Peek(16) == 0xee;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0ea8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s609(s14, gas - 1)
  }

  /** Node 609
    * Segment Id for this node is: 184
    * Starting at 0xea8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s609(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xeca

    requires s0.stack[6] == 0x97c

    requires s0.stack[13] == 0x310

    requires s0.stack[17] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeca;
      assert s1.Peek(6) == 0x97c;
      assert s1.Peek(13) == 0x310;
      assert s1.Peek(17) == 0xee;
      var s2 := Push2(s1, 0x0eb1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e04);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s610(s5, gas - 1)
  }

  /** Node 610
    * Segment Id for this node is: 166
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s610(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xeb1

    requires s0.stack[4] == 0xeca

    requires s0.stack[8] == 0x97c

    requires s0.stack[15] == 0x310

    requires s0.stack[19] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb1;
      assert s1.Peek(4) == 0xeca;
      assert s1.Peek(8) == 0x97c;
      assert s1.Peek(15) == 0x310;
      assert s1.Peek(19) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s611(s9, gas - 1)
  }

  /** Node 611
    * Segment Id for this node is: 185
    * Starting at 0xeb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s611(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xeca

    requires s0.stack[7] == 0x97c

    requires s0.stack[14] == 0x310

    requires s0.stack[18] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xeca;
      assert s1.Peek(7) == 0x97c;
      assert s1.Peek(14) == 0x310;
      assert s1.Peek(18) == 0xee;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s612(s6, gas - 1)
  }

  /** Node 612
    * Segment Id for this node is: 187
    * Starting at 0xeca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s612(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x97c

    requires s0.stack[10] == 0x310

    requires s0.stack[14] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x97c;
      assert s1.Peek(10) == 0x310;
      assert s1.Peek(14) == 0xee;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s613(s6, gas - 1)
  }

  /** Node 613
    * Segment Id for this node is: 118
    * Starting at 0x97c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s613(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x310

    requires s0.stack[11] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x310;
      assert s1.Peek(11) == 0xee;
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
      assert s11.Peek(0) == 0x310;
      assert s11.Peek(4) == 0xee;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s614(s12, gas - 1)
  }

  /** Node 614
    * Segment Id for this node is: 69
    * Starting at 0x310
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s614(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x310 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s615(s9, gas - 1)
  }

  /** Node 615
    * Segment Id for this node is: 23
    * Starting at 0xee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s615(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00fb);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0e8f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s616(s8, gas - 1)
  }

  /** Node 616
    * Segment Id for this node is: 182
    * Starting at 0xe8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s616(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xfb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfb;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0ea2);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xea2;
      assert s11.Peek(5) == 0xfb;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e80);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s617(s14, gas - 1)
  }

  /** Node 617
    * Segment Id for this node is: 180
    * Starting at 0xe80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s617(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xea2

    requires s0.stack[6] == 0xfb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xea2;
      assert s1.Peek(6) == 0xfb;
      var s2 := Push2(s1, 0x0e89);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s618(s5, gas - 1)
  }

  /** Node 618
    * Segment Id for this node is: 179
    * Starting at 0xe75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s618(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe89

    requires s0.stack[4] == 0xea2

    requires s0.stack[8] == 0xfb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe89;
      assert s1.Peek(4) == 0xea2;
      assert s1.Peek(8) == 0xfb;
      var s2 := Push0(s1);
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
      ExecuteFromCFGNode_s619(s11, gas - 1)
  }

  /** Node 619
    * Segment Id for this node is: 181
    * Starting at 0xe89
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s619(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xea2

    requires s0.stack[7] == 0xfb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xea2;
      assert s1.Peek(7) == 0xfb;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s620(s6, gas - 1)
  }

  /** Node 620
    * Segment Id for this node is: 183
    * Starting at 0xea2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s620(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xfb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfb;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s621(s6, gas - 1)
  }

  /** Node 621
    * Segment Id for this node is: 24
    * Starting at 0xfb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s621(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb as nat
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

  /** Node 622
    * Segment Id for this node is: 18
    * Starting at 0xb6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s622(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00be);
      var s3 := Push2(s2, 0x0274);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s623(s4, gas - 1)
  }

  /** Node 623
    * Segment Id for this node is: 59
    * Starting at 0x274
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s623(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x274 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xbe;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x0283);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x103d);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s624(s9, gas - 1)
  }

  /** Node 624
    * Segment Id for this node is: 221
    * Starting at 0x103d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s624(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x283

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x283;
      assert s1.Peek(4) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x283;
      assert s11.Peek(7) == 0xbe;
      var s12 := Push2(s11, 0x1054);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s626(s13, gas - 1)
      else
        ExecuteFromCFGNode_s625(s13, gas - 1)
  }

  /** Node 625
    * Segment Id for this node is: 222
    * Starting at 0x104e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s625(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x283

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x283;
      assert s1.Peek(7) == 0xbe;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s626(s5, gas - 1)
  }

  /** Node 626
    * Segment Id for this node is: 223
    * Starting at 0x1054
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s626(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x283

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x283;
      assert s1.Peek(6) == 0xbe;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x1067);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s629(s8, gas - 1)
      else
        ExecuteFromCFGNode_s627(s8, gas - 1)
  }

  /** Node 627
    * Segment Id for this node is: 224
    * Starting at 0x105f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s627(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x283

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1066);
      assert s1.Peek(0) == 0x1066;
      assert s1.Peek(4) == 0x283;
      assert s1.Peek(7) == 0xbe;
      var s2 := Push2(s1, 0x1010);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s628(s3, gas - 1)
  }

  /** Node 628
    * Segment Id for this node is: 220
    * Starting at 0x1010
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s628(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1010 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x1066

    requires s0.stack[4] == 0x283

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1066;
      assert s1.Peek(4) == 0x283;
      assert s1.Peek(7) == 0xbe;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 629
    * Segment Id for this node is: 226
    * Starting at 0x1067
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s629(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1067 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x283

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x283;
      assert s1.Peek(6) == 0xbe;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s630(s6, gas - 1)
  }

  /** Node 630
    * Segment Id for this node is: 60
    * Starting at 0x283
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s630(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x283 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbe;
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
      assert s11.Peek(4) == 0xbe;
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
      assert s21.Peek(5) == 0xbe;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x02af);
      assert s31.Peek(0) == 0x2af;
      assert s31.Peek(8) == 0xbe;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x103d);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s631(s34, gas - 1)
  }

  /** Node 631
    * Segment Id for this node is: 221
    * Starting at 0x103d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s631(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x2af

    requires s0.stack[8] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2af;
      assert s1.Peek(8) == 0xbe;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x2af;
      assert s11.Peek(11) == 0xbe;
      var s12 := Push2(s11, 0x1054);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s633(s13, gas - 1)
      else
        ExecuteFromCFGNode_s632(s13, gas - 1)
  }

  /** Node 632
    * Segment Id for this node is: 222
    * Starting at 0x104e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s632(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2af

    requires s0.stack[10] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x2af;
      assert s1.Peek(11) == 0xbe;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s633(s5, gas - 1)
  }

  /** Node 633
    * Segment Id for this node is: 223
    * Starting at 0x1054
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s633(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1054 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2af

    requires s0.stack[10] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2af;
      assert s1.Peek(10) == 0xbe;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x1067);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s636(s8, gas - 1)
      else
        ExecuteFromCFGNode_s634(s8, gas - 1)
  }

  /** Node 634
    * Segment Id for this node is: 224
    * Starting at 0x105f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s634(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2af

    requires s0.stack[10] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1066);
      assert s1.Peek(0) == 0x1066;
      assert s1.Peek(4) == 0x2af;
      assert s1.Peek(11) == 0xbe;
      var s2 := Push2(s1, 0x1010);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s635(s3, gas - 1)
  }

  /** Node 635
    * Segment Id for this node is: 220
    * Starting at 0x1010
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s635(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1010 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x1066

    requires s0.stack[4] == 0x2af

    requires s0.stack[11] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1066;
      assert s1.Peek(4) == 0x2af;
      assert s1.Peek(11) == 0xbe;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 636
    * Segment Id for this node is: 226
    * Starting at 0x1067
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s636(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1067 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2af

    requires s0.stack[10] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2af;
      assert s1.Peek(10) == 0xbe;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s637(s6, gas - 1)
  }

  /** Node 637
    * Segment Id for this node is: 61
    * Starting at 0x2af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s637(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xbe;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x02fa);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s640(s5, gas - 1)
      else
        ExecuteFromCFGNode_s638(s5, gas - 1)
  }

  /** Node 638
    * Segment Id for this node is: 62
    * Starting at 0x2b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s638(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0xbe;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x02d1);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s657(s5, gas - 1)
      else
        ExecuteFromCFGNode_s639(s5, gas - 1)
  }

  /** Node 639
    * Segment Id for this node is: 63
    * Starting at 0x2be
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s639(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0xbe;
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
      assert s11.Peek(7) == 0xbe;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x02fa);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s640(s14, gas - 1)
  }

  /** Node 640
    * Segment Id for this node is: 67
    * Starting at 0x2fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s640(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xbe;
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
      ExecuteFromCFGNode_s641(s10, gas - 1)
  }

  /** Node 641
    * Segment Id for this node is: 19
    * Starting at 0xbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s641(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00cb);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d86);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s642(s8, gas - 1)
  }

  /** Node 642
    * Segment Id for this node is: 154
    * Starting at 0xd86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s642(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcb;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(5) == 0xcb;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0d9e);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0d4e);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s643(s19, gas - 1)
  }

  /** Node 643
    * Segment Id for this node is: 149
    * Starting at 0xd4e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s643(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd9e

    requires s0.stack[6] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd9e;
      assert s1.Peek(6) == 0xcb;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d58);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0cfc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s644(s6, gas - 1)
  }

  /** Node 644
    * Segment Id for this node is: 142
    * Starting at 0xcfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s644(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xd58

    requires s0.stack[5] == 0xd9e

    requires s0.stack[9] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd58;
      assert s1.Peek(5) == 0xd9e;
      assert s1.Peek(9) == 0xcb;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s645(s10, gas - 1)
  }

  /** Node 645
    * Segment Id for this node is: 150
    * Starting at 0xd58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s645(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xd9e

    requires s0.stack[8] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd9e;
      assert s1.Peek(8) == 0xcb;
      var s2 := Push2(s1, 0x0d62);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s646(s6, gas - 1)
  }

  /** Node 646
    * Segment Id for this node is: 143
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s646(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xd62

    requires s0.stack[7] == 0xd9e

    requires s0.stack[11] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd62;
      assert s1.Peek(7) == 0xd9e;
      assert s1.Peek(11) == 0xcb;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xd62;
      assert s11.Peek(8) == 0xd9e;
      assert s11.Peek(12) == 0xcb;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s647(s15, gas - 1)
  }

  /** Node 647
    * Segment Id for this node is: 151
    * Starting at 0xd62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s647(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xd9e

    requires s0.stack[9] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd9e;
      assert s1.Peek(9) == 0xcb;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0d72);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0d16);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s648(s11, gas - 1)
  }

  /** Node 648
    * Segment Id for this node is: 144
    * Starting at 0xd16
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s648(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xd72

    requires s0.stack[8] == 0xd9e

    requires s0.stack[12] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd72;
      assert s1.Peek(8) == 0xd9e;
      assert s1.Peek(12) == 0xcb;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s649(s2, gas - 1)
  }

  /** Node 649
    * Segment Id for this node is: 145
    * Starting at 0xd18
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s649(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd72

    requires s0.stack[9] == 0xd9e

    requires s0.stack[13] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd72;
      assert s1.Peek(9) == 0xd9e;
      assert s1.Peek(13) == 0xcb;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0d33);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s651(s7, gas - 1)
      else
        ExecuteFromCFGNode_s650(s7, gas - 1)
  }

  /** Node 650
    * Segment Id for this node is: 146
    * Starting at 0xd21
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s650(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd21 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd72

    requires s0.stack[9] == 0xd9e

    requires s0.stack[13] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xd72;
      assert s1.Peek(10) == 0xd9e;
      assert s1.Peek(14) == 0xcb;
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
      assert s11.Peek(5) == 0xd72;
      assert s11.Peek(10) == 0xd9e;
      assert s11.Peek(14) == 0xcb;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0d18);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s649(s15, gas - 1)
  }

  /** Node 651
    * Segment Id for this node is: 147
    * Starting at 0xd33
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s651(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd72

    requires s0.stack[9] == 0xd9e

    requires s0.stack[13] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd72;
      assert s1.Peek(9) == 0xd9e;
      assert s1.Peek(13) == 0xcb;
      var s2 := Push0(s1);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s652(s11, gas - 1)
  }

  /** Node 652
    * Segment Id for this node is: 152
    * Starting at 0xd72
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s652(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xd9e

    requires s0.stack[8] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd9e;
      assert s1.Peek(8) == 0xcb;
      var s2 := Push2(s1, 0x0d7b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d3e);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s653(s5, gas - 1)
  }

  /** Node 653
    * Segment Id for this node is: 148
    * Starting at 0xd3e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s653(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xd7b

    requires s0.stack[6] == 0xd9e

    requires s0.stack[10] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd7b;
      assert s1.Peek(6) == 0xd9e;
      assert s1.Peek(10) == 0xcb;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xd7b;
      assert s11.Peek(7) == 0xd9e;
      assert s11.Peek(11) == 0xcb;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s654(s14, gas - 1)
  }

  /** Node 654
    * Segment Id for this node is: 153
    * Starting at 0xd7b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s654(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xd9e

    requires s0.stack[9] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd9e;
      assert s1.Peek(9) == 0xcb;
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
      ExecuteFromCFGNode_s655(s11, gas - 1)
  }

  /** Node 655
    * Segment Id for this node is: 155
    * Starting at 0xd9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s655(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xcb;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s656(s8, gas - 1)
  }

  /** Node 656
    * Segment Id for this node is: 20
    * Starting at 0xcb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s656(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb as nat
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

  /** Node 657
    * Segment Id for this node is: 64
    * Starting at 0x2d1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s657(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xbe;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Push0(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Push0(s8);
      var s10 := Keccak256(s9);
      var s11 := Swap1(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s658(s11, gas - 1)
  }

  /** Node 658
    * Segment Id for this node is: 65
    * Starting at 0x2dd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s658(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xbe;
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
      assert s11.Peek(7) == 0xbe;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x02dd);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s658(s16, gas - 1)
      else
        ExecuteFromCFGNode_s659(s16, gas - 1)
  }

  /** Node 659
    * Segment Id for this node is: 66
    * Starting at 0x2f1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s659(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0xbe;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s640(s8, gas - 1)
  }

  /** Node 660
    * Segment Id for this node is: 17
    * Starting at 0xb2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s660(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2 as nat
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