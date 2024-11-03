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
        ExecuteFromCFGNode_s582(s7, gas - 1)
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
      var s6 := Push4(s5, 0x715018a6);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x006f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s266(s9, gas - 1)
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
      var s2 := Push4(s1, 0x715018a6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01a0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s242(s5, gas - 1)
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
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01aa);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s5, gas - 1)
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
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01c8);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01e6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s96(s5, gas - 1)
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
      var s4 := Push2(s3, 0x0216);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s5, gas - 1)
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
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0246);
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
    * Segment Id for this node is: 55
    * Starting at 0x246
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x246 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0260);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x025b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x25b;
      assert s11.Peek(3) == 0x260;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0eb0);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s14, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 210
    * Starting at 0xeb0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x25b

    requires s0.stack[3] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x25b;
      assert s1.Peek(3) == 0x260;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ec5);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s10, gas - 1)
      else
        ExecuteFromCFGNode_s14(s10, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 211
    * Starting at 0xebd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x25b

    requires s0.stack[4] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ec4);
      assert s1.Peek(0) == 0xec4;
      assert s1.Peek(4) == 0x25b;
      assert s1.Peek(5) == 0x260;
      var s2 := Push2(s1, 0x0d02);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s3, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 166
    * Starting at 0xd02
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0xec4

    requires s0.stack[4] == 0x25b

    requires s0.stack[5] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xec4;
      assert s1.Peek(4) == 0x25b;
      assert s1.Peek(5) == 0x260;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 16
    * Segment Id for this node is: 213
    * Starting at 0xec5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x25b

    requires s0.stack[4] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x25b;
      assert s1.Peek(4) == 0x260;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0ed2);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d4c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s9, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 174
    * Starting at 0xd4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xed2

    requires s0.stack[7] == 0x25b

    requires s0.stack[8] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xed2;
      assert s1.Peek(7) == 0x25b;
      assert s1.Peek(8) == 0x260;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d5a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d36);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s10, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 170
    * Starting at 0xd36
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xed2

    requires s0.stack[10] == 0x25b

    requires s0.stack[11] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xed2;
      assert s1.Peek(10) == 0x25b;
      assert s1.Peek(11) == 0x260;
      var s2 := Push2(s1, 0x0d3f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s5, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd3f

    requires s0.stack[3] == 0xd5a

    requires s0.stack[7] == 0xed2

    requires s0.stack[12] == 0x25b

    requires s0.stack[13] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd3f;
      assert s1.Peek(3) == 0xd5a;
      assert s1.Peek(7) == 0xed2;
      assert s1.Peek(12) == 0x25b;
      assert s1.Peek(13) == 0x260;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s6, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xd3f

    requires s0.stack[6] == 0xd5a

    requires s0.stack[10] == 0xed2

    requires s0.stack[15] == 0x25b

    requires s0.stack[16] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xd3f;
      assert s1.Peek(6) == 0xd5a;
      assert s1.Peek(10) == 0xed2;
      assert s1.Peek(15) == 0x25b;
      assert s1.Peek(16) == 0x260;
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
      ExecuteFromCFGNode_s21(s11, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xd3f

    requires s0.stack[5] == 0xd5a

    requires s0.stack[9] == 0xed2

    requires s0.stack[14] == 0x25b

    requires s0.stack[15] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3f;
      assert s1.Peek(5) == 0xd5a;
      assert s1.Peek(9) == 0xed2;
      assert s1.Peek(14) == 0x25b;
      assert s1.Peek(15) == 0x260;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s7, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 171
    * Starting at 0xd3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xd5a

    requires s0.stack[6] == 0xed2

    requires s0.stack[11] == 0x25b

    requires s0.stack[12] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xed2;
      assert s1.Peek(11) == 0x25b;
      assert s1.Peek(12) == 0x260;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d49);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s5, gas - 1)
      else
        ExecuteFromCFGNode_s23(s5, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 172
    * Starting at 0xd46
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xed2

    requires s0.stack[10] == 0x25b

    requires s0.stack[11] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xed2;
      assert s1.Peek(11) == 0x25b;
      assert s1.Peek(12) == 0x260;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 24
    * Segment Id for this node is: 173
    * Starting at 0xd49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xed2

    requires s0.stack[10] == 0x25b

    requires s0.stack[11] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xed2;
      assert s1.Peek(10) == 0x25b;
      assert s1.Peek(11) == 0x260;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s3, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 175
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xed2

    requires s0.stack[8] == 0x25b

    requires s0.stack[9] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xed2;
      assert s1.Peek(8) == 0x25b;
      assert s1.Peek(9) == 0x260;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s6, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 214
    * Starting at 0xed2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x25b

    requires s0.stack[6] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x25b;
      assert s1.Peek(6) == 0x260;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s9, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 56
    * Starting at 0x25b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x260;
      var s2 := Push2(s1, 0x0507);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s3, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 95
    * Starting at 0x507
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x507 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x260;
      var s2 := Push2(s1, 0x050f);
      var s3 := Push2(s2, 0x0726);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s4, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 120
    * Starting at 0x726
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x726 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x50f

    requires s0.stack[2] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x50f;
      assert s1.Peek(2) == 0x260;
      var s2 := Push2(s1, 0x072e);
      var s3 := Push2(s2, 0x058b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s4, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 101
    * Starting at 0x58b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x72e

    requires s0.stack[1] == 0x50f

    requires s0.stack[3] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x72e;
      assert s1.Peek(1) == 0x50f;
      assert s1.Peek(3) == 0x260;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s7, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 121
    * Starting at 0x72e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x50f

    requires s0.stack[3] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x50f;
      assert s1.Peek(3) == 0x260;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x074c);
      var s5 := Push2(s4, 0x03ab);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s6, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 80
    * Starting at 0x3ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x74c

    requires s0.stack[2] == 0x50f

    requires s0.stack[4] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x74c;
      assert s1.Peek(2) == 0x50f;
      assert s1.Peek(4) == 0x260;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x74c;
      assert s11.Peek(4) == 0x50f;
      assert s11.Peek(6) == 0x260;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s17, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 122
    * Starting at 0x74c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x50f

    requires s0.stack[4] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x50f;
      assert s1.Peek(4) == 0x260;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x07ab);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s6, gas - 1)
      else
        ExecuteFromCFGNode_s34(s6, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 123
    * Starting at 0x768
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x768 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x50f

    requires s0.stack[2] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x076f);
      assert s1.Peek(0) == 0x76f;
      assert s1.Peek(1) == 0x50f;
      assert s1.Peek(3) == 0x260;
      var s2 := Push2(s1, 0x058b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s3, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 101
    * Starting at 0x58b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x76f

    requires s0.stack[1] == 0x50f

    requires s0.stack[3] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x76f;
      assert s1.Peek(1) == 0x50f;
      assert s1.Peek(3) == 0x260;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s7, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 124
    * Starting at 0x76f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x50f

    requires s0.stack[3] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x50f;
      assert s1.Peek(3) == 0x260;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x118cdaa700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x07a2);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x7a2;
      assert s11.Peek(3) == 0x50f;
      assert s11.Peek(5) == 0x260;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s13, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x7a2

    requires s0.stack[3] == 0x50f

    requires s0.stack[5] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7a2;
      assert s1.Peek(3) == 0x50f;
      assert s1.Peek(5) == 0x260;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x7a2;
      assert s11.Peek(6) == 0x50f;
      assert s11.Peek(8) == 0x260;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s14, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x7a2

    requires s0.stack[7] == 0x50f

    requires s0.stack[9] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x7a2;
      assert s1.Peek(7) == 0x50f;
      assert s1.Peek(9) == 0x260;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s5, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x7a2

    requires s0.stack[9] == 0x50f

    requires s0.stack[11] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x7a2;
      assert s1.Peek(9) == 0x50f;
      assert s1.Peek(11) == 0x260;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s6, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x7a2

    requires s0.stack[12] == 0x50f

    requires s0.stack[14] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x7a2;
      assert s1.Peek(12) == 0x50f;
      assert s1.Peek(14) == 0x260;
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
      ExecuteFromCFGNode_s41(s11, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x7a2

    requires s0.stack[11] == 0x50f

    requires s0.stack[13] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x7a2;
      assert s1.Peek(11) == 0x50f;
      assert s1.Peek(13) == 0x260;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s7, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x7a2

    requires s0.stack[8] == 0x50f

    requires s0.stack[10] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x7a2;
      assert s1.Peek(8) == 0x50f;
      assert s1.Peek(10) == 0x260;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s6, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x7a2

    requires s0.stack[4] == 0x50f

    requires s0.stack[6] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7a2;
      assert s1.Peek(4) == 0x50f;
      assert s1.Peek(6) == 0x260;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s6, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 125
    * Starting at 0x7a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x50f

    requires s0.stack[3] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x50f;
      assert s1.Peek(3) == 0x260;
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

  /** Node 45
    * Segment Id for this node is: 126
    * Starting at 0x7ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x50f

    requires s0.stack[2] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x50f;
      assert s1.Peek(2) == 0x260;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s2, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 96
    * Starting at 0x50f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x260;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x057f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s10, gas - 1)
      else
        ExecuteFromCFGNode_s47(s10, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 97
    * Starting at 0x543
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x543 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0x260;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x1e4fbdf700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0576);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x576;
      assert s11.Peek(4) == 0x260;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s13, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x576

    requires s0.stack[4] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x576;
      assert s1.Peek(4) == 0x260;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x576;
      assert s11.Peek(7) == 0x260;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s14, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x576

    requires s0.stack[8] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x576;
      assert s1.Peek(8) == 0x260;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s5, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x576

    requires s0.stack[10] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x576;
      assert s1.Peek(10) == 0x260;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s6, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x576

    requires s0.stack[13] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x576;
      assert s1.Peek(13) == 0x260;
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
      ExecuteFromCFGNode_s52(s11, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x576

    requires s0.stack[12] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x576;
      assert s1.Peek(12) == 0x260;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s7, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x576

    requires s0.stack[9] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x576;
      assert s1.Peek(9) == 0x260;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x576

    requires s0.stack[5] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x576;
      assert s1.Peek(5) == 0x260;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s6, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 98
    * Starting at 0x576
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x576 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x260;
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

  /** Node 56
    * Segment Id for this node is: 99
    * Starting at 0x57f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x260;
      var s2 := Push2(s1, 0x0588);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x07ad);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s5, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 127
    * Starting at 0x7ad
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x588

    requires s0.stack[3] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x588;
      assert s1.Peek(3) == 0x260;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x588;
      assert s11.Peek(5) == 0x260;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x05);
      var s18 := Push0(s17);
      var s19 := Push2(s18, 0x0100);
      var s20 := Exp(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x588;
      assert s21.Peek(8) == 0x260;
      var s22 := SLoad(s21);
      var s23 := Dup2(s22);
      var s24 := Push20(s23, 0xffffffffffffffffffffffffffffffffffffffff);
      var s25 := Mul(s24);
      var s26 := Not(s25);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Dup4(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(7) == 0x588;
      assert s31.Peek(9) == 0x260;
      var s32 := Mul(s31);
      var s33 := Or(s32);
      var s34 := Swap1(s33);
      var s35 := SStore(s34);
      var s36 := Pop(s35);
      var s37 := Dup2(s36);
      var s38 := Push20(s37, 0xffffffffffffffffffffffffffffffffffffffff);
      var s39 := And(s38);
      var s40 := Dup2(s39);
      var s41 := Push20(s40, 0xffffffffffffffffffffffffffffffffffffffff);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s58(s41, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 128
    * Starting at 0x840
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x840 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x588

    requires s0.stack[7] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(4) == 0x588;
      assert s1.Peek(6) == 0x260;
      var s2 := Push32(s1, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Swap2(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Log3(s10);
      assert s11.Peek(2) == 0x588;
      assert s11.Peek(4) == 0x260;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s14, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 100
    * Starting at 0x588
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x588 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x260

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x260;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s3, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 57
    * Starting at 0x260
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x260 as nat
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

  /** Node 61
    * Segment Id for this node is: 51
    * Starting at 0x216
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0230);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x022b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x22b;
      assert s11.Peek(3) == 0x230;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f03);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s14, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 219
    * Starting at 0xf03
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x22b

    requires s0.stack[3] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x22b;
      assert s1.Peek(3) == 0x230;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f19);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s11, gas - 1)
      else
        ExecuteFromCFGNode_s63(s11, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 220
    * Starting at 0xf11
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x22b

    requires s0.stack[5] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f18);
      assert s1.Peek(0) == 0xf18;
      assert s1.Peek(5) == 0x22b;
      assert s1.Peek(6) == 0x230;
      var s2 := Push2(s1, 0x0d02);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s3, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 166
    * Starting at 0xd02
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xf18

    requires s0.stack[5] == 0x22b

    requires s0.stack[6] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf18;
      assert s1.Peek(5) == 0x22b;
      assert s1.Peek(6) == 0x230;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 65
    * Segment Id for this node is: 222
    * Starting at 0xf19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x22b

    requires s0.stack[5] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x22b;
      assert s1.Peek(5) == 0x230;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f26);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d4c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s9, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 174
    * Starting at 0xd4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf26

    requires s0.stack[8] == 0x22b

    requires s0.stack[9] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf26;
      assert s1.Peek(8) == 0x22b;
      assert s1.Peek(9) == 0x230;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d5a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d36);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s10, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 170
    * Starting at 0xd36
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xf26

    requires s0.stack[11] == 0x22b

    requires s0.stack[12] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xf26;
      assert s1.Peek(11) == 0x22b;
      assert s1.Peek(12) == 0x230;
      var s2 := Push2(s1, 0x0d3f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s5, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xd3f

    requires s0.stack[3] == 0xd5a

    requires s0.stack[7] == 0xf26

    requires s0.stack[13] == 0x22b

    requires s0.stack[14] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd3f;
      assert s1.Peek(3) == 0xd5a;
      assert s1.Peek(7) == 0xf26;
      assert s1.Peek(13) == 0x22b;
      assert s1.Peek(14) == 0x230;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s6, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xd3f

    requires s0.stack[6] == 0xd5a

    requires s0.stack[10] == 0xf26

    requires s0.stack[16] == 0x22b

    requires s0.stack[17] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xd3f;
      assert s1.Peek(6) == 0xd5a;
      assert s1.Peek(10) == 0xf26;
      assert s1.Peek(16) == 0x22b;
      assert s1.Peek(17) == 0x230;
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
      ExecuteFromCFGNode_s70(s11, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xd3f

    requires s0.stack[5] == 0xd5a

    requires s0.stack[9] == 0xf26

    requires s0.stack[15] == 0x22b

    requires s0.stack[16] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3f;
      assert s1.Peek(5) == 0xd5a;
      assert s1.Peek(9) == 0xf26;
      assert s1.Peek(15) == 0x22b;
      assert s1.Peek(16) == 0x230;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s7, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 171
    * Starting at 0xd3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd5a

    requires s0.stack[6] == 0xf26

    requires s0.stack[12] == 0x22b

    requires s0.stack[13] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xf26;
      assert s1.Peek(12) == 0x22b;
      assert s1.Peek(13) == 0x230;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d49);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s5, gas - 1)
      else
        ExecuteFromCFGNode_s72(s5, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 172
    * Starting at 0xd46
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xf26

    requires s0.stack[11] == 0x22b

    requires s0.stack[12] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xf26;
      assert s1.Peek(12) == 0x22b;
      assert s1.Peek(13) == 0x230;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 73
    * Segment Id for this node is: 173
    * Starting at 0xd49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xf26

    requires s0.stack[11] == 0x22b

    requires s0.stack[12] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xf26;
      assert s1.Peek(11) == 0x22b;
      assert s1.Peek(12) == 0x230;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s3, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 175
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf26

    requires s0.stack[9] == 0x22b

    requires s0.stack[10] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf26;
      assert s1.Peek(9) == 0x22b;
      assert s1.Peek(10) == 0x230;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s6, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 223
    * Starting at 0xf26
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x22b

    requires s0.stack[7] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x22b;
      assert s1.Peek(7) == 0x230;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0f37);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d4c);
      assert s11.Peek(0) == 0xd4c;
      assert s11.Peek(3) == 0xf37;
      assert s11.Peek(9) == 0x22b;
      assert s11.Peek(10) == 0x230;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s12, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 174
    * Starting at 0xd4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf37

    requires s0.stack[8] == 0x22b

    requires s0.stack[9] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf37;
      assert s1.Peek(8) == 0x22b;
      assert s1.Peek(9) == 0x230;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d5a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d36);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s10, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 170
    * Starting at 0xd36
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xf37

    requires s0.stack[11] == 0x22b

    requires s0.stack[12] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xf37;
      assert s1.Peek(11) == 0x22b;
      assert s1.Peek(12) == 0x230;
      var s2 := Push2(s1, 0x0d3f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s5, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xd3f

    requires s0.stack[3] == 0xd5a

    requires s0.stack[7] == 0xf37

    requires s0.stack[13] == 0x22b

    requires s0.stack[14] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd3f;
      assert s1.Peek(3) == 0xd5a;
      assert s1.Peek(7) == 0xf37;
      assert s1.Peek(13) == 0x22b;
      assert s1.Peek(14) == 0x230;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s6, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xd3f

    requires s0.stack[6] == 0xd5a

    requires s0.stack[10] == 0xf37

    requires s0.stack[16] == 0x22b

    requires s0.stack[17] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xd3f;
      assert s1.Peek(6) == 0xd5a;
      assert s1.Peek(10) == 0xf37;
      assert s1.Peek(16) == 0x22b;
      assert s1.Peek(17) == 0x230;
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
      ExecuteFromCFGNode_s80(s11, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xd3f

    requires s0.stack[5] == 0xd5a

    requires s0.stack[9] == 0xf37

    requires s0.stack[15] == 0x22b

    requires s0.stack[16] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3f;
      assert s1.Peek(5) == 0xd5a;
      assert s1.Peek(9) == 0xf37;
      assert s1.Peek(15) == 0x22b;
      assert s1.Peek(16) == 0x230;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s7, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 171
    * Starting at 0xd3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd5a

    requires s0.stack[6] == 0xf37

    requires s0.stack[12] == 0x22b

    requires s0.stack[13] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xf37;
      assert s1.Peek(12) == 0x22b;
      assert s1.Peek(13) == 0x230;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d49);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s5, gas - 1)
      else
        ExecuteFromCFGNode_s82(s5, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 172
    * Starting at 0xd46
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xf37

    requires s0.stack[11] == 0x22b

    requires s0.stack[12] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xf37;
      assert s1.Peek(12) == 0x22b;
      assert s1.Peek(13) == 0x230;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 83
    * Segment Id for this node is: 173
    * Starting at 0xd49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xf37

    requires s0.stack[11] == 0x22b

    requires s0.stack[12] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xf37;
      assert s1.Peek(11) == 0x22b;
      assert s1.Peek(12) == 0x230;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s3, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 175
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf37

    requires s0.stack[9] == 0x22b

    requires s0.stack[10] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf37;
      assert s1.Peek(9) == 0x22b;
      assert s1.Peek(10) == 0x230;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s6, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 224
    * Starting at 0xf37
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x22b

    requires s0.stack[7] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x22b;
      assert s1.Peek(7) == 0x230;
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
      ExecuteFromCFGNode_s86(s10, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 52
    * Starting at 0x22b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x230;
      var s2 := Push2(s1, 0x0485);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s3, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 93
    * Starting at 0x485
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x485 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x230;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x230;
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
      assert s21.Peek(5) == 0x230;
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
      assert s31.Peek(5) == 0x230;
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
      ExecuteFromCFGNode_s88(s41, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 94
    * Starting at 0x503
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x503 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x230

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x230;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s4, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 53
    * Starting at 0x230
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x230 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x023d);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0e13);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s8, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 196
    * Starting at 0xe13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x23d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x23d;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0e26);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xe26;
      assert s11.Peek(5) == 0x23d;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e04);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s14, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xe26

    requires s0.stack[6] == 0x23d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe26;
      assert s1.Peek(6) == 0x23d;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s5, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xe26

    requires s0.stack[8] == 0x23d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xe26;
      assert s1.Peek(8) == 0x23d;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s9, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xe26

    requires s0.stack[7] == 0x23d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe26;
      assert s1.Peek(7) == 0x23d;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s6, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 197
    * Starting at 0xe26
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x23d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x23d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s6, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 54
    * Starting at 0x23d
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23d as nat
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

  /** Node 96
    * Segment Id for this node is: 47
    * Starting at 0x1e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0200);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x01fb);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x1fb;
      assert s11.Peek(3) == 0x200;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d93);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s14, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 183
    * Starting at 0xd93
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1fb

    requires s0.stack[3] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(3) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0da9);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s11, gas - 1)
      else
        ExecuteFromCFGNode_s98(s11, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 184
    * Starting at 0xda1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1fb

    requires s0.stack[5] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0da8);
      assert s1.Peek(0) == 0xda8;
      assert s1.Peek(5) == 0x1fb;
      assert s1.Peek(6) == 0x200;
      var s2 := Push2(s1, 0x0d02);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s3, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 166
    * Starting at 0xd02
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xda8

    requires s0.stack[5] == 0x1fb

    requires s0.stack[6] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xda8;
      assert s1.Peek(5) == 0x1fb;
      assert s1.Peek(6) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 100
    * Segment Id for this node is: 186
    * Starting at 0xda9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1fb

    requires s0.stack[5] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1fb;
      assert s1.Peek(5) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0db6);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d4c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s9, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 174
    * Starting at 0xd4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xdb6

    requires s0.stack[8] == 0x1fb

    requires s0.stack[9] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb6;
      assert s1.Peek(8) == 0x1fb;
      assert s1.Peek(9) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d5a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d36);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s10, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 170
    * Starting at 0xd36
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xdb6

    requires s0.stack[11] == 0x1fb

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xdb6;
      assert s1.Peek(11) == 0x1fb;
      assert s1.Peek(12) == 0x200;
      var s2 := Push2(s1, 0x0d3f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s5, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xd3f

    requires s0.stack[3] == 0xd5a

    requires s0.stack[7] == 0xdb6

    requires s0.stack[13] == 0x1fb

    requires s0.stack[14] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd3f;
      assert s1.Peek(3) == 0xd5a;
      assert s1.Peek(7) == 0xdb6;
      assert s1.Peek(13) == 0x1fb;
      assert s1.Peek(14) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s6, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xd3f

    requires s0.stack[6] == 0xd5a

    requires s0.stack[10] == 0xdb6

    requires s0.stack[16] == 0x1fb

    requires s0.stack[17] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xd3f;
      assert s1.Peek(6) == 0xd5a;
      assert s1.Peek(10) == 0xdb6;
      assert s1.Peek(16) == 0x1fb;
      assert s1.Peek(17) == 0x200;
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
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xd3f

    requires s0.stack[5] == 0xd5a

    requires s0.stack[9] == 0xdb6

    requires s0.stack[15] == 0x1fb

    requires s0.stack[16] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3f;
      assert s1.Peek(5) == 0xd5a;
      assert s1.Peek(9) == 0xdb6;
      assert s1.Peek(15) == 0x1fb;
      assert s1.Peek(16) == 0x200;
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
    * Segment Id for this node is: 171
    * Starting at 0xd3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd5a

    requires s0.stack[6] == 0xdb6

    requires s0.stack[12] == 0x1fb

    requires s0.stack[13] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xdb6;
      assert s1.Peek(12) == 0x1fb;
      assert s1.Peek(13) == 0x200;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d49);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s5, gas - 1)
      else
        ExecuteFromCFGNode_s107(s5, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 172
    * Starting at 0xd46
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xdb6

    requires s0.stack[11] == 0x1fb

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xdb6;
      assert s1.Peek(12) == 0x1fb;
      assert s1.Peek(13) == 0x200;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 108
    * Segment Id for this node is: 173
    * Starting at 0xd49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xdb6

    requires s0.stack[11] == 0x1fb

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xdb6;
      assert s1.Peek(11) == 0x1fb;
      assert s1.Peek(12) == 0x200;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s3, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 175
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xdb6

    requires s0.stack[9] == 0x1fb

    requires s0.stack[10] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb6;
      assert s1.Peek(9) == 0x1fb;
      assert s1.Peek(10) == 0x200;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s6, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 187
    * Starting at 0xdb6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1fb

    requires s0.stack[7] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1fb;
      assert s1.Peek(7) == 0x200;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0dc7);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d7f);
      assert s11.Peek(0) == 0xd7f;
      assert s11.Peek(3) == 0xdc7;
      assert s11.Peek(9) == 0x1fb;
      assert s11.Peek(10) == 0x200;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s12, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 181
    * Starting at 0xd7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xdc7

    requires s0.stack[8] == 0x1fb

    requires s0.stack[9] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdc7;
      assert s1.Peek(8) == 0x1fb;
      assert s1.Peek(9) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d8d);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d69);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s10, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 177
    * Starting at 0xd69
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd8d

    requires s0.stack[5] == 0xdc7

    requires s0.stack[11] == 0x1fb

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd8d;
      assert s1.Peek(5) == 0xdc7;
      assert s1.Peek(11) == 0x1fb;
      assert s1.Peek(12) == 0x200;
      var s2 := Push2(s1, 0x0d72);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s5, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xd72

    requires s0.stack[3] == 0xd8d

    requires s0.stack[7] == 0xdc7

    requires s0.stack[13] == 0x1fb

    requires s0.stack[14] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd72;
      assert s1.Peek(3) == 0xd8d;
      assert s1.Peek(7) == 0xdc7;
      assert s1.Peek(13) == 0x1fb;
      assert s1.Peek(14) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s9, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 178
    * Starting at 0xd72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd8d

    requires s0.stack[6] == 0xdc7

    requires s0.stack[12] == 0x1fb

    requires s0.stack[13] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd8d;
      assert s1.Peek(6) == 0xdc7;
      assert s1.Peek(12) == 0x1fb;
      assert s1.Peek(13) == 0x200;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d7c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s116(s5, gas - 1)
      else
        ExecuteFromCFGNode_s115(s5, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 179
    * Starting at 0xd79
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd8d

    requires s0.stack[5] == 0xdc7

    requires s0.stack[11] == 0x1fb

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd8d;
      assert s1.Peek(6) == 0xdc7;
      assert s1.Peek(12) == 0x1fb;
      assert s1.Peek(13) == 0x200;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 116
    * Segment Id for this node is: 180
    * Starting at 0xd7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd8d

    requires s0.stack[5] == 0xdc7

    requires s0.stack[11] == 0x1fb

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd8d;
      assert s1.Peek(5) == 0xdc7;
      assert s1.Peek(11) == 0x1fb;
      assert s1.Peek(12) == 0x200;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s3, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 182
    * Starting at 0xd8d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xdc7

    requires s0.stack[9] == 0x1fb

    requires s0.stack[10] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdc7;
      assert s1.Peek(9) == 0x1fb;
      assert s1.Peek(10) == 0x200;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s6, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 188
    * Starting at 0xdc7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1fb

    requires s0.stack[7] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1fb;
      assert s1.Peek(7) == 0x200;
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
      ExecuteFromCFGNode_s119(s10, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 48
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x200;
      var s2 := Push2(s1, 0x0463);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s3, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 90
    * Starting at 0x463
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x046d);
      var s5 := Push2(s4, 0x058b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s6, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 101
    * Starting at 0x58b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x46d

    requires s0.stack[5] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x46d;
      assert s1.Peek(5) == 0x200;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s7, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 91
    * Starting at 0x46d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x200;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x047a);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x0636);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s9, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 112
    * Starting at 0x636
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x636 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47a

    requires s0.stack[8] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x47a;
      assert s1.Peek(8) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a6);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s10, gas - 1)
      else
        ExecuteFromCFGNode_s124(s10, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 113
    * Starting at 0x66a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47a

    requires s0.stack[8] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x47a;
      assert s1.Peek(9) == 0x200;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x96c6fd1e00000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x069d);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x69d;
      assert s11.Peek(6) == 0x47a;
      assert s11.Peek(11) == 0x200;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s13, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x69d

    requires s0.stack[6] == 0x47a

    requires s0.stack[11] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x69d;
      assert s1.Peek(6) == 0x47a;
      assert s1.Peek(11) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x69d;
      assert s11.Peek(9) == 0x47a;
      assert s11.Peek(14) == 0x200;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s14, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x69d

    requires s0.stack[10] == 0x47a

    requires s0.stack[15] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x69d;
      assert s1.Peek(10) == 0x47a;
      assert s1.Peek(15) == 0x200;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s5, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x69d

    requires s0.stack[12] == 0x47a

    requires s0.stack[17] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x69d;
      assert s1.Peek(12) == 0x47a;
      assert s1.Peek(17) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s6, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x69d

    requires s0.stack[15] == 0x47a

    requires s0.stack[20] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x69d;
      assert s1.Peek(15) == 0x47a;
      assert s1.Peek(20) == 0x200;
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
      ExecuteFromCFGNode_s129(s11, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x69d

    requires s0.stack[14] == 0x47a

    requires s0.stack[19] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x69d;
      assert s1.Peek(14) == 0x47a;
      assert s1.Peek(19) == 0x200;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s7, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x69d

    requires s0.stack[11] == 0x47a

    requires s0.stack[16] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x69d;
      assert s1.Peek(11) == 0x47a;
      assert s1.Peek(16) == 0x200;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s6, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x69d

    requires s0.stack[7] == 0x47a

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x69d;
      assert s1.Peek(7) == 0x47a;
      assert s1.Peek(12) == 0x200;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s6, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 114
    * Starting at 0x69d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x47a

    requires s0.stack[9] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x47a;
      assert s1.Peek(9) == 0x200;
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

  /** Node 133
    * Segment Id for this node is: 115
    * Starting at 0x6a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47a

    requires s0.stack[8] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x47a;
      assert s1.Peek(8) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0716);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s10, gas - 1)
      else
        ExecuteFromCFGNode_s134(s10, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 116
    * Starting at 0x6da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47a

    requires s0.stack[8] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x47a;
      assert s1.Peek(9) == 0x200;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xec442f0500000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x070d);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x70d;
      assert s11.Peek(6) == 0x47a;
      assert s11.Peek(11) == 0x200;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s13, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x70d

    requires s0.stack[6] == 0x47a

    requires s0.stack[11] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x70d;
      assert s1.Peek(6) == 0x47a;
      assert s1.Peek(11) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x70d;
      assert s11.Peek(9) == 0x47a;
      assert s11.Peek(14) == 0x200;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s14, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x70d

    requires s0.stack[10] == 0x47a

    requires s0.stack[15] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x70d;
      assert s1.Peek(10) == 0x47a;
      assert s1.Peek(15) == 0x200;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s5, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x70d

    requires s0.stack[12] == 0x47a

    requires s0.stack[17] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x70d;
      assert s1.Peek(12) == 0x47a;
      assert s1.Peek(17) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s6, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x70d

    requires s0.stack[15] == 0x47a

    requires s0.stack[20] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x70d;
      assert s1.Peek(15) == 0x47a;
      assert s1.Peek(20) == 0x200;
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
      ExecuteFromCFGNode_s139(s11, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x70d

    requires s0.stack[14] == 0x47a

    requires s0.stack[19] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x70d;
      assert s1.Peek(14) == 0x47a;
      assert s1.Peek(19) == 0x200;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s7, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x70d

    requires s0.stack[11] == 0x47a

    requires s0.stack[16] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x70d;
      assert s1.Peek(11) == 0x47a;
      assert s1.Peek(16) == 0x200;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s6, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x70d

    requires s0.stack[7] == 0x47a

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x70d;
      assert s1.Peek(7) == 0x47a;
      assert s1.Peek(12) == 0x200;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s6, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 117
    * Starting at 0x70d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x47a

    requires s0.stack[9] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x47a;
      assert s1.Peek(9) == 0x200;
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

  /** Node 143
    * Segment Id for this node is: 118
    * Starting at 0x716
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x716 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47a

    requires s0.stack[8] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x47a;
      assert s1.Peek(8) == 0x200;
      var s2 := Push2(s1, 0x0721);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0a3f);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s7, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 140
    * Starting at 0xa3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x47a

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x721;
      assert s1.Peek(7) == 0x47a;
      assert s1.Peek(12) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0a8f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s10, gas - 1)
      else
        ExecuteFromCFGNode_s145(s10, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 141
    * Starting at 0xa73
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x47a

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x721;
      assert s1.Peek(8) == 0x47a;
      assert s1.Peek(13) == 0x200;
      var s2 := Push1(s1, 0x02);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := SLoad(s5);
      var s7 := Push2(s6, 0x0a83);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1000);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s11, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 237
    * Starting at 0x1000
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1000 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xa83

    requires s0.stack[9] == 0x721

    requires s0.stack[13] == 0x47a

    requires s0.stack[18] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa83;
      assert s1.Peek(9) == 0x721;
      assert s1.Peek(13) == 0x47a;
      assert s1.Peek(18) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x100a);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d60);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s6, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x100a

    requires s0.stack[5] == 0xa83

    requires s0.stack[12] == 0x721

    requires s0.stack[16] == 0x47a

    requires s0.stack[21] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x100a;
      assert s1.Peek(5) == 0xa83;
      assert s1.Peek(12) == 0x721;
      assert s1.Peek(16) == 0x47a;
      assert s1.Peek(21) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s9, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 238
    * Starting at 0x100a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0xa83

    requires s0.stack[11] == 0x721

    requires s0.stack[15] == 0x47a

    requires s0.stack[20] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa83;
      assert s1.Peek(11) == 0x721;
      assert s1.Peek(15) == 0x47a;
      assert s1.Peek(20) == 0x200;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1015);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d60);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s7, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x1015

    requires s0.stack[5] == 0xa83

    requires s0.stack[12] == 0x721

    requires s0.stack[16] == 0x47a

    requires s0.stack[21] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1015;
      assert s1.Peek(5) == 0xa83;
      assert s1.Peek(12) == 0x721;
      assert s1.Peek(16) == 0x47a;
      assert s1.Peek(21) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s9, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 239
    * Starting at 0x1015
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0xa83

    requires s0.stack[11] == 0x721

    requires s0.stack[15] == 0x47a

    requires s0.stack[20] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa83;
      assert s1.Peek(11) == 0x721;
      assert s1.Peek(15) == 0x47a;
      assert s1.Peek(20) == 0x200;
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
      assert s11.Peek(4) == 0xa83;
      assert s11.Peek(11) == 0x721;
      assert s11.Peek(15) == 0x47a;
      assert s11.Peek(20) == 0x200;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x102d);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s153(s14, gas - 1)
      else
        ExecuteFromCFGNode_s151(s14, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 240
    * Starting at 0x1025
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1025 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xa83

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x47a

    requires s0.stack[19] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x102c);
      assert s1.Peek(0) == 0x102c;
      assert s1.Peek(4) == 0xa83;
      assert s1.Peek(11) == 0x721;
      assert s1.Peek(15) == 0x47a;
      assert s1.Peek(20) == 0x200;
      var s2 := Push2(s1, 0x0fd3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s3, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 236
    * Starting at 0xfd3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x102c

    requires s0.stack[4] == 0xa83

    requires s0.stack[11] == 0x721

    requires s0.stack[15] == 0x47a

    requires s0.stack[20] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x102c;
      assert s1.Peek(4) == 0xa83;
      assert s1.Peek(11) == 0x721;
      assert s1.Peek(15) == 0x47a;
      assert s1.Peek(20) == 0x200;
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

  /** Node 153
    * Segment Id for this node is: 242
    * Starting at 0x102d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xa83

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x47a

    requires s0.stack[19] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa83;
      assert s1.Peek(10) == 0x721;
      assert s1.Peek(14) == 0x47a;
      assert s1.Peek(19) == 0x200;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s6, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 142
    * Starting at 0xa83
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0x721

    requires s0.stack[11] == 0x47a

    requires s0.stack[16] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x721;
      assert s1.Peek(11) == 0x47a;
      assert s1.Peek(16) == 0x200;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Push2(s8, 0x0b5d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s10, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 147
    * Starting at 0xb5d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x47a

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x721;
      assert s1.Peek(7) == 0x47a;
      assert s1.Peek(12) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0ba4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s173(s10, gas - 1)
      else
        ExecuteFromCFGNode_s156(s10, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 148
    * Starting at 0xb91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x47a

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x721;
      assert s1.Peek(8) == 0x47a;
      assert s1.Peek(13) == 0x200;
      var s2 := Push1(s1, 0x02);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := SLoad(s5);
      var s7 := Sub(s6);
      var s8 := Swap3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x721;
      assert s11.Peek(10) == 0x47a;
      assert s11.Peek(15) == 0x200;
      var s12 := Swap1(s11);
      var s13 := SStore(s12);
      var s14 := Pop(s13);
      var s15 := Push2(s14, 0x0bee);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s16, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 150
    * Starting at 0xbee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x47a

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x721;
      assert s1.Peek(7) == 0x47a;
      assert s1.Peek(12) == 0x200;
      var s2 := Dup2(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push32(s7, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s9 := Dup4(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(8) == 0x721;
      assert s11.Peek(12) == 0x47a;
      assert s11.Peek(17) == 0x200;
      var s12 := Push2(s11, 0x0c4b);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x0e13);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s16, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 196
    * Starting at 0xe13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xc4b

    requires s0.stack[9] == 0x721

    requires s0.stack[13] == 0x47a

    requires s0.stack[18] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc4b;
      assert s1.Peek(9) == 0x721;
      assert s1.Peek(13) == 0x47a;
      assert s1.Peek(18) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0e26);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xe26;
      assert s11.Peek(5) == 0xc4b;
      assert s11.Peek(12) == 0x721;
      assert s11.Peek(16) == 0x47a;
      assert s11.Peek(21) == 0x200;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e04);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s14, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xe26

    requires s0.stack[6] == 0xc4b

    requires s0.stack[13] == 0x721

    requires s0.stack[17] == 0x47a

    requires s0.stack[22] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe26;
      assert s1.Peek(6) == 0xc4b;
      assert s1.Peek(13) == 0x721;
      assert s1.Peek(17) == 0x47a;
      assert s1.Peek(22) == 0x200;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s5, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xe26

    requires s0.stack[8] == 0xc4b

    requires s0.stack[15] == 0x721

    requires s0.stack[19] == 0x47a

    requires s0.stack[24] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xe26;
      assert s1.Peek(8) == 0xc4b;
      assert s1.Peek(15) == 0x721;
      assert s1.Peek(19) == 0x47a;
      assert s1.Peek(24) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s9, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xe26

    requires s0.stack[7] == 0xc4b

    requires s0.stack[14] == 0x721

    requires s0.stack[18] == 0x47a

    requires s0.stack[23] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe26;
      assert s1.Peek(7) == 0xc4b;
      assert s1.Peek(14) == 0x721;
      assert s1.Peek(18) == 0x47a;
      assert s1.Peek(23) == 0x200;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s6, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 197
    * Starting at 0xe26
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xc4b

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x47a

    requires s0.stack[19] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc4b;
      assert s1.Peek(10) == 0x721;
      assert s1.Peek(14) == 0x47a;
      assert s1.Peek(19) == 0x200;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s6, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 151
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0x721

    requires s0.stack[11] == 0x47a

    requires s0.stack[16] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x721;
      assert s1.Peek(11) == 0x47a;
      assert s1.Peek(16) == 0x200;
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
      assert s11.Peek(0) == 0x721;
      assert s11.Peek(4) == 0x47a;
      assert s11.Peek(9) == 0x200;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s12, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 119
    * Starting at 0x721
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x721 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47a

    requires s0.stack[8] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x47a;
      assert s1.Peek(8) == 0x200;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s5, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 92
    * Starting at 0x47a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x200;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s10, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 49
    * Starting at 0x200
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x200 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x020d);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0deb);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s8, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 192
    * Starting at 0xdeb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdeb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0dfe);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xdfe;
      assert s11.Peek(5) == 0x20d;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0ddc);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s14, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 190
    * Starting at 0xddc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xddc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0x20d;
      var s2 := Push2(s1, 0x0de5);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dd1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s5, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 189
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xde5

    requires s0.stack[4] == 0xdfe

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde5;
      assert s1.Peek(4) == 0xdfe;
      assert s1.Peek(8) == 0x20d;
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
      ExecuteFromCFGNode_s170(s11, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 191
    * Starting at 0xde5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s6, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 193
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s6, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 50
    * Starting at 0x20d
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20d as nat
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
    * Segment Id for this node is: 149
    * Starting at 0xba4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x47a

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x721;
      assert s1.Peek(7) == 0x47a;
      assert s1.Peek(12) == 0x200;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Dup1(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x721;
      assert s11.Peek(10) == 0x47a;
      assert s11.Peek(15) == 0x200;
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
      assert s21.Peek(6) == 0x721;
      assert s21.Peek(10) == 0x47a;
      assert s21.Peek(15) == 0x200;
      var s22 := Dup3(s21);
      var s23 := Dup3(s22);
      var s24 := SLoad(s23);
      var s25 := Add(s24);
      var s26 := Swap3(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := SStore(s30);
      assert s31.Peek(4) == 0x721;
      assert s31.Peek(8) == 0x47a;
      assert s31.Peek(13) == 0x200;
      var s32 := Pop(s31);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s157(s32, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 143
    * Starting at 0xa8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x47a

    requires s0.stack[12] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x721;
      assert s1.Peek(7) == 0x47a;
      assert s1.Peek(12) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x721;
      assert s11.Peek(10) == 0x47a;
      assert s11.Peek(15) == 0x200;
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
      assert s21.Peek(5) == 0x721;
      assert s21.Peek(9) == 0x47a;
      assert s21.Peek(14) == 0x200;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0b18);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s192(s29, gas - 1)
      else
        ExecuteFromCFGNode_s175(s29, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 144
    * Starting at 0xad8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x721

    requires s0.stack[8] == 0x47a

    requires s0.stack[13] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(5) == 0x721;
      assert s1.Peek(9) == 0x47a;
      assert s1.Peek(14) == 0x200;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xe450d38c00000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0b0f);
      assert s11.Peek(0) == 0xb0f;
      assert s11.Peek(9) == 0x721;
      assert s11.Peek(13) == 0x47a;
      assert s11.Peek(18) == 0x200;
      var s12 := Swap4(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Push2(s15, 0x0f9e);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s17, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 232
    * Starting at 0xf9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xb0f

    requires s0.stack[9] == 0x721

    requires s0.stack[13] == 0x47a

    requires s0.stack[18] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb0f;
      assert s1.Peek(9) == 0x721;
      assert s1.Peek(13) == 0x47a;
      assert s1.Peek(18) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0fb1);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xfb1;
      assert s11.Peek(7) == 0xb0f;
      assert s11.Peek(12) == 0x721;
      assert s11.Peek(16) == 0x47a;
      assert s11.Peek(21) == 0x200;
      var s12 := Dup7(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s14, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xfb1

    requires s0.stack[8] == 0xb0f

    requires s0.stack[13] == 0x721

    requires s0.stack[17] == 0x47a

    requires s0.stack[22] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfb1;
      assert s1.Peek(8) == 0xb0f;
      assert s1.Peek(13) == 0x721;
      assert s1.Peek(17) == 0x47a;
      assert s1.Peek(22) == 0x200;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s5, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xfb1

    requires s0.stack[10] == 0xb0f

    requires s0.stack[15] == 0x721

    requires s0.stack[19] == 0x47a

    requires s0.stack[24] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xfb1;
      assert s1.Peek(10) == 0xb0f;
      assert s1.Peek(15) == 0x721;
      assert s1.Peek(19) == 0x47a;
      assert s1.Peek(24) == 0x200;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s6, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xfb1

    requires s0.stack[13] == 0xb0f

    requires s0.stack[18] == 0x721

    requires s0.stack[22] == 0x47a

    requires s0.stack[27] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xfb1;
      assert s1.Peek(13) == 0xb0f;
      assert s1.Peek(18) == 0x721;
      assert s1.Peek(22) == 0x47a;
      assert s1.Peek(27) == 0x200;
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
      ExecuteFromCFGNode_s180(s11, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xfb1

    requires s0.stack[12] == 0xb0f

    requires s0.stack[17] == 0x721

    requires s0.stack[21] == 0x47a

    requires s0.stack[26] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xfb1;
      assert s1.Peek(12) == 0xb0f;
      assert s1.Peek(17) == 0x721;
      assert s1.Peek(21) == 0x47a;
      assert s1.Peek(26) == 0x200;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s7, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xfb1

    requires s0.stack[9] == 0xb0f

    requires s0.stack[14] == 0x721

    requires s0.stack[18] == 0x47a

    requires s0.stack[23] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfb1;
      assert s1.Peek(9) == 0xb0f;
      assert s1.Peek(14) == 0x721;
      assert s1.Peek(18) == 0x47a;
      assert s1.Peek(23) == 0x200;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s6, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 233
    * Starting at 0xfb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0xb0f

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x47a

    requires s0.stack[19] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xb0f;
      assert s1.Peek(10) == 0x721;
      assert s1.Peek(14) == 0x47a;
      assert s1.Peek(19) == 0x200;
      var s2 := Push2(s1, 0x0fbe);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup6(s5);
      var s7 := Push2(s6, 0x0e04);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s8, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xfbe

    requires s0.stack[8] == 0xb0f

    requires s0.stack[13] == 0x721

    requires s0.stack[17] == 0x47a

    requires s0.stack[22] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfbe;
      assert s1.Peek(8) == 0xb0f;
      assert s1.Peek(13) == 0x721;
      assert s1.Peek(17) == 0x47a;
      assert s1.Peek(22) == 0x200;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s5, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xfbe

    requires s0.stack[10] == 0xb0f

    requires s0.stack[15] == 0x721

    requires s0.stack[19] == 0x47a

    requires s0.stack[24] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xfbe;
      assert s1.Peek(10) == 0xb0f;
      assert s1.Peek(15) == 0x721;
      assert s1.Peek(19) == 0x47a;
      assert s1.Peek(24) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s9, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xfbe

    requires s0.stack[9] == 0xb0f

    requires s0.stack[14] == 0x721

    requires s0.stack[18] == 0x47a

    requires s0.stack[23] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfbe;
      assert s1.Peek(9) == 0xb0f;
      assert s1.Peek(14) == 0x721;
      assert s1.Peek(18) == 0x47a;
      assert s1.Peek(23) == 0x200;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s6, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 234
    * Starting at 0xfbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0xb0f

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x47a

    requires s0.stack[19] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xb0f;
      assert s1.Peek(10) == 0x721;
      assert s1.Peek(14) == 0x47a;
      assert s1.Peek(19) == 0x200;
      var s2 := Push2(s1, 0x0fcb);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0e04);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s8, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xfcb

    requires s0.stack[8] == 0xb0f

    requires s0.stack[13] == 0x721

    requires s0.stack[17] == 0x47a

    requires s0.stack[22] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfcb;
      assert s1.Peek(8) == 0xb0f;
      assert s1.Peek(13) == 0x721;
      assert s1.Peek(17) == 0x47a;
      assert s1.Peek(22) == 0x200;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s5, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xfcb

    requires s0.stack[10] == 0xb0f

    requires s0.stack[15] == 0x721

    requires s0.stack[19] == 0x47a

    requires s0.stack[24] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xfcb;
      assert s1.Peek(10) == 0xb0f;
      assert s1.Peek(15) == 0x721;
      assert s1.Peek(19) == 0x47a;
      assert s1.Peek(24) == 0x200;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s9, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xfcb

    requires s0.stack[9] == 0xb0f

    requires s0.stack[14] == 0x721

    requires s0.stack[18] == 0x47a

    requires s0.stack[23] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfcb;
      assert s1.Peek(9) == 0xb0f;
      assert s1.Peek(14) == 0x721;
      assert s1.Peek(18) == 0x47a;
      assert s1.Peek(23) == 0x200;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s6, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 235
    * Starting at 0xfcb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0xb0f

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x47a

    requires s0.stack[19] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xb0f;
      assert s1.Peek(10) == 0x721;
      assert s1.Peek(14) == 0x47a;
      assert s1.Peek(19) == 0x200;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s8, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 145
    * Starting at 0xb0f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x721

    requires s0.stack[9] == 0x47a

    requires s0.stack[14] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x721;
      assert s1.Peek(9) == 0x47a;
      assert s1.Peek(14) == 0x200;
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

  /** Node 192
    * Segment Id for this node is: 146
    * Starting at 0xb18
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x721

    requires s0.stack[8] == 0x47a

    requires s0.stack[13] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x721;
      assert s1.Peek(8) == 0x47a;
      assert s1.Peek(13) == 0x200;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push0(s4);
      var s6 := Dup1(s5);
      var s7 := Dup7(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x721;
      assert s11.Peek(12) == 0x47a;
      assert s11.Peek(17) == 0x200;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push0(s20);
      assert s21.Peek(7) == 0x721;
      assert s21.Peek(11) == 0x47a;
      assert s21.Peek(16) == 0x200;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s155(s27, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 44
    * Starting at 0x1c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01d0);
      var s3 := Push2(s2, 0x03d3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s4, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 81
    * Starting at 0x3d3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1d0;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x03e2);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0f6e);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s9, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 226
    * Starting at 0xf6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x3e2

    requires s0.stack[4] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3e2;
      assert s1.Peek(4) == 0x1d0;
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
      assert s11.Peek(4) == 0x3e2;
      assert s11.Peek(7) == 0x1d0;
      var s12 := Push2(s11, 0x0f85);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s13, gas - 1)
      else
        ExecuteFromCFGNode_s196(s13, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 227
    * Starting at 0xf7f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3e2

    requires s0.stack[6] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x3e2;
      assert s1.Peek(7) == 0x1d0;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s197(s5, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 228
    * Starting at 0xf85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3e2

    requires s0.stack[6] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e2;
      assert s1.Peek(6) == 0x1d0;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0f98);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s200(s8, gas - 1)
      else
        ExecuteFromCFGNode_s198(s8, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 229
    * Starting at 0xf90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3e2

    requires s0.stack[6] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f97);
      assert s1.Peek(0) == 0xf97;
      assert s1.Peek(4) == 0x3e2;
      assert s1.Peek(7) == 0x1d0;
      var s2 := Push2(s1, 0x0f41);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s3, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 225
    * Starting at 0xf41
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xf97

    requires s0.stack[4] == 0x3e2

    requires s0.stack[7] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf97;
      assert s1.Peek(4) == 0x3e2;
      assert s1.Peek(7) == 0x1d0;
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

  /** Node 200
    * Segment Id for this node is: 231
    * Starting at 0xf98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3e2

    requires s0.stack[6] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e2;
      assert s1.Peek(6) == 0x1d0;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s6, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 82
    * Starting at 0x3e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1d0;
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
      assert s11.Peek(4) == 0x1d0;
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
      assert s21.Peek(5) == 0x1d0;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x040e);
      assert s31.Peek(0) == 0x40e;
      assert s31.Peek(8) == 0x1d0;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0f6e);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s34, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 226
    * Starting at 0xf6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x40e

    requires s0.stack[8] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x40e;
      assert s1.Peek(8) == 0x1d0;
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
      assert s11.Peek(4) == 0x40e;
      assert s11.Peek(11) == 0x1d0;
      var s12 := Push2(s11, 0x0f85);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s13, gas - 1)
      else
        ExecuteFromCFGNode_s203(s13, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 227
    * Starting at 0xf7f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x40e

    requires s0.stack[10] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x40e;
      assert s1.Peek(11) == 0x1d0;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s204(s5, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 228
    * Starting at 0xf85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x40e

    requires s0.stack[10] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x40e;
      assert s1.Peek(10) == 0x1d0;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0f98);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s207(s8, gas - 1)
      else
        ExecuteFromCFGNode_s205(s8, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 229
    * Starting at 0xf90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x40e

    requires s0.stack[10] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f97);
      assert s1.Peek(0) == 0xf97;
      assert s1.Peek(4) == 0x40e;
      assert s1.Peek(11) == 0x1d0;
      var s2 := Push2(s1, 0x0f41);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s3, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 225
    * Starting at 0xf41
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xf97

    requires s0.stack[4] == 0x40e

    requires s0.stack[11] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf97;
      assert s1.Peek(4) == 0x40e;
      assert s1.Peek(11) == 0x1d0;
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

  /** Node 207
    * Segment Id for this node is: 231
    * Starting at 0xf98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x40e

    requires s0.stack[10] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x40e;
      assert s1.Peek(10) == 0x1d0;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s6, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 83
    * Starting at 0x40e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1d0;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0459);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s211(s5, gas - 1)
      else
        ExecuteFromCFGNode_s209(s5, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 84
    * Starting at 0x415
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x415 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0x1d0;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0430);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s228(s5, gas - 1)
      else
        ExecuteFromCFGNode_s210(s5, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 85
    * Starting at 0x41d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0x1d0;
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
      assert s11.Peek(7) == 0x1d0;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0459);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s14, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 89
    * Starting at 0x459
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x459 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1d0;
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
      ExecuteFromCFGNode_s212(s10, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 45
    * Starting at 0x1d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01dd);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0ce2);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s8, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 164
    * Starting at 0xce2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1dd;
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
      assert s11.Peek(5) == 0x1dd;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0cfa);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0caa);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s19, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 159
    * Starting at 0xcaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xcfa

    requires s0.stack[6] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcfa;
      assert s1.Peek(6) == 0x1dd;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0cb4);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c58);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s6, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 152
    * Starting at 0xc58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xcb4

    requires s0.stack[5] == 0xcfa

    requires s0.stack[9] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcb4;
      assert s1.Peek(5) == 0xcfa;
      assert s1.Peek(9) == 0x1dd;
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
      ExecuteFromCFGNode_s216(s10, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 160
    * Starting at 0xcb4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xcfa

    requires s0.stack[8] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xcfa;
      assert s1.Peek(8) == 0x1dd;
      var s2 := Push2(s1, 0x0cbe);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0c62);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s6, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 153
    * Starting at 0xc62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xcbe

    requires s0.stack[7] == 0xcfa

    requires s0.stack[11] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcbe;
      assert s1.Peek(7) == 0xcfa;
      assert s1.Peek(11) == 0x1dd;
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
      assert s11.Peek(0) == 0xcbe;
      assert s11.Peek(8) == 0xcfa;
      assert s11.Peek(12) == 0x1dd;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s15, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 161
    * Starting at 0xcbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xcfa

    requires s0.stack[9] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xcfa;
      assert s1.Peek(9) == 0x1dd;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0cce);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0c72);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s11, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 154
    * Starting at 0xc72
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xcce

    requires s0.stack[8] == 0xcfa

    requires s0.stack[12] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcce;
      assert s1.Peek(8) == 0xcfa;
      assert s1.Peek(12) == 0x1dd;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s220(s2, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 155
    * Starting at 0xc74
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xcce

    requires s0.stack[9] == 0xcfa

    requires s0.stack[13] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xcce;
      assert s1.Peek(9) == 0xcfa;
      assert s1.Peek(13) == 0x1dd;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c8f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s222(s7, gas - 1)
      else
        ExecuteFromCFGNode_s221(s7, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 156
    * Starting at 0xc7d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xcce

    requires s0.stack[9] == 0xcfa

    requires s0.stack[13] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xcce;
      assert s1.Peek(10) == 0xcfa;
      assert s1.Peek(14) == 0x1dd;
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
      assert s11.Peek(5) == 0xcce;
      assert s11.Peek(10) == 0xcfa;
      assert s11.Peek(14) == 0x1dd;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0c74);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s15, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 157
    * Starting at 0xc8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xcce

    requires s0.stack[9] == 0xcfa

    requires s0.stack[13] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xcce;
      assert s1.Peek(9) == 0xcfa;
      assert s1.Peek(13) == 0x1dd;
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
      ExecuteFromCFGNode_s223(s11, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 162
    * Starting at 0xcce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xcfa

    requires s0.stack[8] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xcfa;
      assert s1.Peek(8) == 0x1dd;
      var s2 := Push2(s1, 0x0cd7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c9a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s5, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 158
    * Starting at 0xc9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xcd7

    requires s0.stack[6] == 0xcfa

    requires s0.stack[10] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcd7;
      assert s1.Peek(6) == 0xcfa;
      assert s1.Peek(10) == 0x1dd;
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
      assert s11.Peek(0) == 0xcd7;
      assert s11.Peek(7) == 0xcfa;
      assert s11.Peek(11) == 0x1dd;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s14, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 163
    * Starting at 0xcd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xcfa

    requires s0.stack[9] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xcfa;
      assert s1.Peek(9) == 0x1dd;
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
      ExecuteFromCFGNode_s226(s11, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 165
    * Starting at 0xcfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1dd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1dd;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s8, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 46
    * Starting at 0x1dd
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dd as nat
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

  /** Node 228
    * Segment Id for this node is: 86
    * Starting at 0x430
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x430 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1d0;
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
      ExecuteFromCFGNode_s229(s11, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 87
    * Starting at 0x43c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1d0;
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
      assert s11.Peek(7) == 0x1d0;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x043c);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s229(s16, gas - 1)
      else
        ExecuteFromCFGNode_s230(s16, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 88
    * Starting at 0x450
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x450 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1d0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0x1d0;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s211(s8, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 41
    * Starting at 0x1aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01b2);
      var s3 := Push2(s2, 0x03ab);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s4, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 80
    * Starting at 0x3ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1b2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1b2;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x1b2;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s17, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 42
    * Starting at 0x1b2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01bf);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0eea);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s8, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1bf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1bf;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x1bf;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s14, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x1bf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x1bf;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s5, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x1bf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x1bf;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s6, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x1bf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x1bf;
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
      ExecuteFromCFGNode_s238(s11, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x1bf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x1bf;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s7, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x1bf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x1bf;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s240(s6, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1bf

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1bf;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s6, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 43
    * Starting at 0x1bf
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1bf as nat
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

  /** Node 242
    * Segment Id for this node is: 39
    * Starting at 0x1a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push2(s2, 0x0398);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s4, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 77
    * Starting at 0x398
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x398 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1a8;
      var s2 := Push2(s1, 0x03a0);
      var s3 := Push2(s2, 0x0726);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s4, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 120
    * Starting at 0x726
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x726 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x3a0

    requires s0.stack[1] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3a0;
      assert s1.Peek(1) == 0x1a8;
      var s2 := Push2(s1, 0x072e);
      var s3 := Push2(s2, 0x058b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s4, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 101
    * Starting at 0x58b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x72e

    requires s0.stack[1] == 0x3a0

    requires s0.stack[2] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x72e;
      assert s1.Peek(1) == 0x3a0;
      assert s1.Peek(2) == 0x1a8;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s7, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 121
    * Starting at 0x72e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x3a0

    requires s0.stack[2] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3a0;
      assert s1.Peek(2) == 0x1a8;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x074c);
      var s5 := Push2(s4, 0x03ab);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s247(s6, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 80
    * Starting at 0x3ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x74c

    requires s0.stack[2] == 0x3a0

    requires s0.stack[3] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x74c;
      assert s1.Peek(2) == 0x3a0;
      assert s1.Peek(3) == 0x1a8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x74c;
      assert s11.Peek(4) == 0x3a0;
      assert s11.Peek(5) == 0x1a8;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s17, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 122
    * Starting at 0x74c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x3a0

    requires s0.stack[3] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3a0;
      assert s1.Peek(3) == 0x1a8;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x07ab);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s260(s6, gas - 1)
      else
        ExecuteFromCFGNode_s249(s6, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 123
    * Starting at 0x768
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x768 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x3a0

    requires s0.stack[1] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x076f);
      assert s1.Peek(0) == 0x76f;
      assert s1.Peek(1) == 0x3a0;
      assert s1.Peek(2) == 0x1a8;
      var s2 := Push2(s1, 0x058b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s3, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 101
    * Starting at 0x58b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x76f

    requires s0.stack[1] == 0x3a0

    requires s0.stack[2] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x76f;
      assert s1.Peek(1) == 0x3a0;
      assert s1.Peek(2) == 0x1a8;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s7, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 124
    * Starting at 0x76f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x3a0

    requires s0.stack[2] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3a0;
      assert s1.Peek(2) == 0x1a8;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x118cdaa700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x07a2);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x7a2;
      assert s11.Peek(3) == 0x3a0;
      assert s11.Peek(4) == 0x1a8;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s13, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x7a2

    requires s0.stack[3] == 0x3a0

    requires s0.stack[4] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7a2;
      assert s1.Peek(3) == 0x3a0;
      assert s1.Peek(4) == 0x1a8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x7a2;
      assert s11.Peek(6) == 0x3a0;
      assert s11.Peek(7) == 0x1a8;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s14, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x7a2

    requires s0.stack[7] == 0x3a0

    requires s0.stack[8] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x7a2;
      assert s1.Peek(7) == 0x3a0;
      assert s1.Peek(8) == 0x1a8;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s5, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x7a2

    requires s0.stack[9] == 0x3a0

    requires s0.stack[10] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x7a2;
      assert s1.Peek(9) == 0x3a0;
      assert s1.Peek(10) == 0x1a8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s6, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x7a2

    requires s0.stack[12] == 0x3a0

    requires s0.stack[13] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x7a2;
      assert s1.Peek(12) == 0x3a0;
      assert s1.Peek(13) == 0x1a8;
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
      ExecuteFromCFGNode_s256(s11, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x7a2

    requires s0.stack[11] == 0x3a0

    requires s0.stack[12] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x7a2;
      assert s1.Peek(11) == 0x3a0;
      assert s1.Peek(12) == 0x1a8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s7, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x7a2

    requires s0.stack[8] == 0x3a0

    requires s0.stack[9] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x7a2;
      assert s1.Peek(8) == 0x3a0;
      assert s1.Peek(9) == 0x1a8;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s258(s6, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x7a2

    requires s0.stack[4] == 0x3a0

    requires s0.stack[5] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7a2;
      assert s1.Peek(4) == 0x3a0;
      assert s1.Peek(5) == 0x1a8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s6, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 125
    * Starting at 0x7a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x3a0

    requires s0.stack[2] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3a0;
      assert s1.Peek(2) == 0x1a8;
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

  /** Node 260
    * Segment Id for this node is: 126
    * Starting at 0x7ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x3a0

    requires s0.stack[1] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3a0;
      assert s1.Peek(1) == 0x1a8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s2, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 78
    * Starting at 0x3a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1a8;
      var s2 := Push2(s1, 0x03a9);
      var s3 := Push0(s2);
      var s4 := Push2(s3, 0x07ad);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s5, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 127
    * Starting at 0x7ad
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x3a9

    requires s0.stack[2] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3a9;
      assert s1.Peek(2) == 0x1a8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x3a9;
      assert s11.Peek(4) == 0x1a8;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x05);
      var s18 := Push0(s17);
      var s19 := Push2(s18, 0x0100);
      var s20 := Exp(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x3a9;
      assert s21.Peek(7) == 0x1a8;
      var s22 := SLoad(s21);
      var s23 := Dup2(s22);
      var s24 := Push20(s23, 0xffffffffffffffffffffffffffffffffffffffff);
      var s25 := Mul(s24);
      var s26 := Not(s25);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Dup4(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(7) == 0x3a9;
      assert s31.Peek(8) == 0x1a8;
      var s32 := Mul(s31);
      var s33 := Or(s32);
      var s34 := Swap1(s33);
      var s35 := SStore(s34);
      var s36 := Pop(s35);
      var s37 := Dup2(s36);
      var s38 := Push20(s37, 0xffffffffffffffffffffffffffffffffffffffff);
      var s39 := And(s38);
      var s40 := Dup2(s39);
      var s41 := Push20(s40, 0xffffffffffffffffffffffffffffffffffffffff);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s263(s41, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 128
    * Starting at 0x840
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x840 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x3a9

    requires s0.stack[6] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(4) == 0x3a9;
      assert s1.Peek(5) == 0x1a8;
      var s2 := Push32(s1, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Swap2(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Log3(s10);
      assert s11.Peek(2) == 0x3a9;
      assert s11.Peek(3) == 0x1a8;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s14, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 79
    * Starting at 0x3a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1a8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s2, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 40
    * Starting at 0x1a8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a8 as nat
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

  /** Node 266
    * Segment Id for this node is: 11
    * Starting at 0x6f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
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
        ExecuteFromCFGNode_s544(s6, gas - 1)
      else
        ExecuteFromCFGNode_s267(s6, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 12
    * Starting at 0x7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
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
        ExecuteFromCFGNode_s477(s5, gas - 1)
      else
        ExecuteFromCFGNode_s268(s5, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 13
    * Starting at 0x86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
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
        ExecuteFromCFGNode_s468(s5, gas - 1)
      else
        ExecuteFromCFGNode_s269(s5, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 14
    * Starting at 0x91
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
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
        ExecuteFromCFGNode_s305(s5, gas - 1)
      else
        ExecuteFromCFGNode_s270(s5, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 15
    * Starting at 0x9c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
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
        ExecuteFromCFGNode_s296(s5, gas - 1)
      else
        ExecuteFromCFGNode_s271(s5, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 16
    * Starting at 0xa7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
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
        ExecuteFromCFGNode_s272(s5, gas - 1)
      else
        ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 35
    * Starting at 0x170
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
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
      var s13 := Push2(s12, 0x0eb0);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s14, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 210
    * Starting at 0xeb0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb0 as nat
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
      var s9 := Push2(s8, 0x0ec5);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s276(s10, gas - 1)
      else
        ExecuteFromCFGNode_s274(s10, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 211
    * Starting at 0xebd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x185

    requires s0.stack[4] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ec4);
      assert s1.Peek(0) == 0xec4;
      assert s1.Peek(4) == 0x185;
      assert s1.Peek(5) == 0x18a;
      var s2 := Push2(s1, 0x0d02);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s3, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 166
    * Starting at 0xd02
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0xec4

    requires s0.stack[4] == 0x185

    requires s0.stack[5] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xec4;
      assert s1.Peek(4) == 0x185;
      assert s1.Peek(5) == 0x18a;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 276
    * Segment Id for this node is: 213
    * Starting at 0xec5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec5 as nat
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
      var s3 := Push2(s2, 0x0ed2);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d4c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s9, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 174
    * Starting at 0xd4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xed2

    requires s0.stack[7] == 0x185

    requires s0.stack[8] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xed2;
      assert s1.Peek(7) == 0x185;
      assert s1.Peek(8) == 0x18a;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d5a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d36);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s278(s10, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 170
    * Starting at 0xd36
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xed2

    requires s0.stack[10] == 0x185

    requires s0.stack[11] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xed2;
      assert s1.Peek(10) == 0x185;
      assert s1.Peek(11) == 0x18a;
      var s2 := Push2(s1, 0x0d3f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s5, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd3f

    requires s0.stack[3] == 0xd5a

    requires s0.stack[7] == 0xed2

    requires s0.stack[12] == 0x185

    requires s0.stack[13] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd3f;
      assert s1.Peek(3) == 0xd5a;
      assert s1.Peek(7) == 0xed2;
      assert s1.Peek(12) == 0x185;
      assert s1.Peek(13) == 0x18a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s6, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xd3f

    requires s0.stack[6] == 0xd5a

    requires s0.stack[10] == 0xed2

    requires s0.stack[15] == 0x185

    requires s0.stack[16] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xd3f;
      assert s1.Peek(6) == 0xd5a;
      assert s1.Peek(10) == 0xed2;
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
      ExecuteFromCFGNode_s281(s11, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xd3f

    requires s0.stack[5] == 0xd5a

    requires s0.stack[9] == 0xed2

    requires s0.stack[14] == 0x185

    requires s0.stack[15] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3f;
      assert s1.Peek(5) == 0xd5a;
      assert s1.Peek(9) == 0xed2;
      assert s1.Peek(14) == 0x185;
      assert s1.Peek(15) == 0x18a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s7, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 171
    * Starting at 0xd3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xd5a

    requires s0.stack[6] == 0xed2

    requires s0.stack[11] == 0x185

    requires s0.stack[12] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xed2;
      assert s1.Peek(11) == 0x185;
      assert s1.Peek(12) == 0x18a;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d49);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s284(s5, gas - 1)
      else
        ExecuteFromCFGNode_s283(s5, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 172
    * Starting at 0xd46
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xed2

    requires s0.stack[10] == 0x185

    requires s0.stack[11] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xed2;
      assert s1.Peek(11) == 0x185;
      assert s1.Peek(12) == 0x18a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 284
    * Segment Id for this node is: 173
    * Starting at 0xd49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xed2

    requires s0.stack[10] == 0x185

    requires s0.stack[11] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xed2;
      assert s1.Peek(10) == 0x185;
      assert s1.Peek(11) == 0x18a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s3, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 175
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xed2

    requires s0.stack[8] == 0x185

    requires s0.stack[9] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xed2;
      assert s1.Peek(8) == 0x185;
      assert s1.Peek(9) == 0x18a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s6, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 214
    * Starting at 0xed2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed2 as nat
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
      ExecuteFromCFGNode_s287(s9, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 36
    * Starting at 0x185
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
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
      var s2 := Push2(s1, 0x0353);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s288(s3, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 76
    * Starting at 0x353
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x353 as nat
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
      var s3 := Dup1(s2);
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
      ExecuteFromCFGNode_s289(s27, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 37
    * Starting at 0x18a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
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
      var s7 := Push2(s6, 0x0e13);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s290(s8, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 196
    * Starting at 0xe13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe13 as nat
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
      var s8 := Push2(s7, 0x0e26);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xe26;
      assert s11.Peek(5) == 0x197;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e04);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s291(s14, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xe26

    requires s0.stack[6] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe26;
      assert s1.Peek(6) == 0x197;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s5, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xe26

    requires s0.stack[8] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xe26;
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
      ExecuteFromCFGNode_s293(s9, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xe26

    requires s0.stack[7] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe26;
      assert s1.Peek(7) == 0x197;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s294(s6, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 197
    * Starting at 0xe26
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe26 as nat
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
      ExecuteFromCFGNode_s295(s6, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 38
    * Starting at 0x197
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
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

  /** Node 296
    * Segment Id for this node is: 32
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push2(s2, 0x034b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s297(s4, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 75
    * Starting at 0x34b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34b as nat
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
      var s3 := Push1(s2, 0x12);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s298(s7, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 33
    * Starting at 0x15a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
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
      var s7 := Push2(s6, 0x0e97);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s8, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 208
    * Starting at 0xe97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe97 as nat
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
      var s8 := Push2(s7, 0x0eaa);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xeaa;
      assert s11.Peek(5) == 0x167;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e88);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s300(s14, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 206
    * Starting at 0xe88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xeaa

    requires s0.stack[6] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeaa;
      assert s1.Peek(6) == 0x167;
      var s2 := Push2(s1, 0x0e91);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0e7c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s301(s5, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 205
    * Starting at 0xe7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe91

    requires s0.stack[4] == 0xeaa

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe91;
      assert s1.Peek(4) == 0xeaa;
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
      ExecuteFromCFGNode_s302(s11, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 207
    * Starting at 0xe91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xeaa

    requires s0.stack[7] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xeaa;
      assert s1.Peek(7) == 0x167;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s303(s6, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 209
    * Starting at 0xeaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeaa as nat
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
      ExecuteFromCFGNode_s304(s6, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 34
    * Starting at 0x167
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
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

  /** Node 305
    * Segment Id for this node is: 28
    * Starting at 0x122
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
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
      var s13 := Push2(s12, 0x0e2c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s306(s14, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 198
    * Starting at 0xe2c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2c as nat
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
      var s11 := Push2(s10, 0x0e43);
      assert s11.Peek(0) == 0xe43;
      assert s11.Peek(7) == 0x137;
      assert s11.Peek(8) == 0x13c;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s309(s12, gas - 1)
      else
        ExecuteFromCFGNode_s307(s12, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 199
    * Starting at 0xe3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x137

    requires s0.stack[6] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e42);
      assert s1.Peek(0) == 0xe42;
      assert s1.Peek(6) == 0x137;
      assert s1.Peek(7) == 0x13c;
      var s2 := Push2(s1, 0x0d02);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s3, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 166
    * Starting at 0xd02
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xe42

    requires s0.stack[6] == 0x137

    requires s0.stack[7] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe42;
      assert s1.Peek(6) == 0x137;
      assert s1.Peek(7) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 309
    * Segment Id for this node is: 201
    * Starting at 0xe43
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe43 as nat
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
      var s3 := Push2(s2, 0x0e50);
      var s4 := Dup7(s3);
      var s5 := Dup3(s4);
      var s6 := Dup8(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d4c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s9, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 174
    * Starting at 0xd4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xe50

    requires s0.stack[9] == 0x137

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe50;
      assert s1.Peek(9) == 0x137;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d5a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d36);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s10, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 170
    * Starting at 0xd36
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xe50

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xe50;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push2(s1, 0x0d3f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s312(s5, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xd3f

    requires s0.stack[3] == 0xd5a

    requires s0.stack[7] == 0xe50

    requires s0.stack[14] == 0x137

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd3f;
      assert s1.Peek(3) == 0xd5a;
      assert s1.Peek(7) == 0xe50;
      assert s1.Peek(14) == 0x137;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s313(s6, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xd3f

    requires s0.stack[6] == 0xd5a

    requires s0.stack[10] == 0xe50

    requires s0.stack[17] == 0x137

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xd3f;
      assert s1.Peek(6) == 0xd5a;
      assert s1.Peek(10) == 0xe50;
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
      ExecuteFromCFGNode_s314(s11, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd3f

    requires s0.stack[5] == 0xd5a

    requires s0.stack[9] == 0xe50

    requires s0.stack[16] == 0x137

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3f;
      assert s1.Peek(5) == 0xd5a;
      assert s1.Peek(9) == 0xe50;
      assert s1.Peek(16) == 0x137;
      assert s1.Peek(17) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s7, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 171
    * Starting at 0xd3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xd5a

    requires s0.stack[6] == 0xe50

    requires s0.stack[13] == 0x137

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xe50;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d49);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s317(s5, gas - 1)
      else
        ExecuteFromCFGNode_s316(s5, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 172
    * Starting at 0xd46
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xe50

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xe50;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 317
    * Segment Id for this node is: 173
    * Starting at 0xd49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xe50

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xe50;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s318(s3, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 175
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xe50

    requires s0.stack[10] == 0x137

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe50;
      assert s1.Peek(10) == 0x137;
      assert s1.Peek(11) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s319(s6, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 202
    * Starting at 0xe50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe50 as nat
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
      var s6 := Push2(s5, 0x0e61);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d4c);
      assert s11.Peek(0) == 0xd4c;
      assert s11.Peek(3) == 0xe61;
      assert s11.Peek(10) == 0x137;
      assert s11.Peek(11) == 0x13c;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s320(s12, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 174
    * Starting at 0xd4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xe61

    requires s0.stack[9] == 0x137

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe61;
      assert s1.Peek(9) == 0x137;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d5a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d36);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s10, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 170
    * Starting at 0xd36
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xe61

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xe61;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push2(s1, 0x0d3f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s322(s5, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xd3f

    requires s0.stack[3] == 0xd5a

    requires s0.stack[7] == 0xe61

    requires s0.stack[14] == 0x137

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd3f;
      assert s1.Peek(3) == 0xd5a;
      assert s1.Peek(7) == 0xe61;
      assert s1.Peek(14) == 0x137;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s6, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xd3f

    requires s0.stack[6] == 0xd5a

    requires s0.stack[10] == 0xe61

    requires s0.stack[17] == 0x137

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xd3f;
      assert s1.Peek(6) == 0xd5a;
      assert s1.Peek(10) == 0xe61;
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
      ExecuteFromCFGNode_s324(s11, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd3f

    requires s0.stack[5] == 0xd5a

    requires s0.stack[9] == 0xe61

    requires s0.stack[16] == 0x137

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3f;
      assert s1.Peek(5) == 0xd5a;
      assert s1.Peek(9) == 0xe61;
      assert s1.Peek(16) == 0x137;
      assert s1.Peek(17) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s325(s7, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 171
    * Starting at 0xd3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xd5a

    requires s0.stack[6] == 0xe61

    requires s0.stack[13] == 0x137

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xe61;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d49);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s327(s5, gas - 1)
      else
        ExecuteFromCFGNode_s326(s5, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 172
    * Starting at 0xd46
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xe61

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xe61;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 327
    * Segment Id for this node is: 173
    * Starting at 0xd49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xe61

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xe61;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s3, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 175
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xe61

    requires s0.stack[10] == 0x137

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe61;
      assert s1.Peek(10) == 0x137;
      assert s1.Peek(11) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s329(s6, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 203
    * Starting at 0xe61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe61 as nat
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
      var s6 := Push2(s5, 0x0e72);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d7f);
      assert s11.Peek(0) == 0xd7f;
      assert s11.Peek(3) == 0xe72;
      assert s11.Peek(10) == 0x137;
      assert s11.Peek(11) == 0x13c;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s12, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 181
    * Starting at 0xd7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xe72

    requires s0.stack[9] == 0x137

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe72;
      assert s1.Peek(9) == 0x137;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d8d);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d69);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s331(s10, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 177
    * Starting at 0xd69
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd8d

    requires s0.stack[5] == 0xe72

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd8d;
      assert s1.Peek(5) == 0xe72;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push2(s1, 0x0d72);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s332(s5, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xd72

    requires s0.stack[3] == 0xd8d

    requires s0.stack[7] == 0xe72

    requires s0.stack[14] == 0x137

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd72;
      assert s1.Peek(3) == 0xd8d;
      assert s1.Peek(7) == 0xe72;
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
      ExecuteFromCFGNode_s333(s9, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 178
    * Starting at 0xd72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xd8d

    requires s0.stack[6] == 0xe72

    requires s0.stack[13] == 0x137

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd8d;
      assert s1.Peek(6) == 0xe72;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d7c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s335(s5, gas - 1)
      else
        ExecuteFromCFGNode_s334(s5, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 179
    * Starting at 0xd79
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd8d

    requires s0.stack[5] == 0xe72

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd8d;
      assert s1.Peek(6) == 0xe72;
      assert s1.Peek(13) == 0x137;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 335
    * Segment Id for this node is: 180
    * Starting at 0xd7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd8d

    requires s0.stack[5] == 0xe72

    requires s0.stack[12] == 0x137

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd8d;
      assert s1.Peek(5) == 0xe72;
      assert s1.Peek(12) == 0x137;
      assert s1.Peek(13) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s3, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 182
    * Starting at 0xd8d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xe72

    requires s0.stack[10] == 0x137

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe72;
      assert s1.Peek(10) == 0x137;
      assert s1.Peek(11) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s6, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 204
    * Starting at 0xe72
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe72 as nat
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
      ExecuteFromCFGNode_s338(s10, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 29
    * Starting at 0x137
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
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
      var s2 := Push2(s1, 0x031d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s3, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 71
    * Starting at 0x31d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31d as nat
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
      var s4 := Push2(s3, 0x0327);
      var s5 := Push2(s4, 0x058b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s340(s6, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 101
    * Starting at 0x58b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x327

    requires s0.stack[6] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x327;
      assert s1.Peek(6) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s7, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 72
    * Starting at 0x327
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x327 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0334);
      var s5 := Dup6(s4);
      var s6 := Dup3(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x05a4);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s342(s9, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 104
    * Starting at 0x5a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x334

    requires s0.stack[9] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x334;
      assert s1.Peek(9) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x05af);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0485);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s343(s7, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 93
    * Starting at 0x485
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x485 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x5af

    requires s0.stack[7] == 0x334

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5af;
      assert s1.Peek(7) == 0x334;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x5af;
      assert s11.Peek(10) == 0x334;
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
      assert s21.Peek(5) == 0x5af;
      assert s21.Peek(10) == 0x334;
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
      assert s31.Peek(5) == 0x5af;
      assert s31.Peek(10) == 0x334;
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
      ExecuteFromCFGNode_s344(s41, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 94
    * Starting at 0x503
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x503 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x5af

    requires s0.stack[8] == 0x334

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x5af;
      assert s1.Peek(8) == 0x334;
      assert s1.Peek(14) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s345(s4, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 105
    * Starting at 0x5af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x334

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x334;
      assert s1.Peek(11) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x0630);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s396(s8, gas - 1)
      else
        ExecuteFromCFGNode_s346(s8, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 106
    * Starting at 0x5d9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x334

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x334;
      assert s1.Peek(11) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0621);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s364(s6, gas - 1)
      else
        ExecuteFromCFGNode_s347(s6, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 107
    * Starting at 0x5e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x334

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(5) == 0x334;
      assert s1.Peek(11) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xfb8f41b200000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0618);
      assert s11.Peek(0) == 0x618;
      assert s11.Peek(9) == 0x334;
      assert s11.Peek(15) == 0x13c;
      var s12 := Swap4(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Push2(s15, 0x0f9e);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s348(s17, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 232
    * Starting at 0xf9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x618

    requires s0.stack[9] == 0x334

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x618;
      assert s1.Peek(9) == 0x334;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0fb1);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xfb1;
      assert s11.Peek(7) == 0x618;
      assert s11.Peek(12) == 0x334;
      assert s11.Peek(18) == 0x13c;
      var s12 := Dup7(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s349(s14, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xfb1

    requires s0.stack[8] == 0x618

    requires s0.stack[13] == 0x334

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfb1;
      assert s1.Peek(8) == 0x618;
      assert s1.Peek(13) == 0x334;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s5, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xfb1

    requires s0.stack[10] == 0x618

    requires s0.stack[15] == 0x334

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xfb1;
      assert s1.Peek(10) == 0x618;
      assert s1.Peek(15) == 0x334;
      assert s1.Peek(21) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s351(s6, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xfb1

    requires s0.stack[13] == 0x618

    requires s0.stack[18] == 0x334

    requires s0.stack[24] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xfb1;
      assert s1.Peek(13) == 0x618;
      assert s1.Peek(18) == 0x334;
      assert s1.Peek(24) == 0x13c;
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
      ExecuteFromCFGNode_s352(s11, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xfb1

    requires s0.stack[12] == 0x618

    requires s0.stack[17] == 0x334

    requires s0.stack[23] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xfb1;
      assert s1.Peek(12) == 0x618;
      assert s1.Peek(17) == 0x334;
      assert s1.Peek(23) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s7, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xfb1

    requires s0.stack[9] == 0x618

    requires s0.stack[14] == 0x334

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfb1;
      assert s1.Peek(9) == 0x618;
      assert s1.Peek(14) == 0x334;
      assert s1.Peek(20) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s354(s6, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 233
    * Starting at 0xfb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x618

    requires s0.stack[10] == 0x334

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x618;
      assert s1.Peek(10) == 0x334;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push2(s1, 0x0fbe);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup6(s5);
      var s7 := Push2(s6, 0x0e04);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s8, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xfbe

    requires s0.stack[8] == 0x618

    requires s0.stack[13] == 0x334

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfbe;
      assert s1.Peek(8) == 0x618;
      assert s1.Peek(13) == 0x334;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s5, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xfbe

    requires s0.stack[10] == 0x618

    requires s0.stack[15] == 0x334

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xfbe;
      assert s1.Peek(10) == 0x618;
      assert s1.Peek(15) == 0x334;
      assert s1.Peek(21) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s9, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xfbe

    requires s0.stack[9] == 0x618

    requires s0.stack[14] == 0x334

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfbe;
      assert s1.Peek(9) == 0x618;
      assert s1.Peek(14) == 0x334;
      assert s1.Peek(20) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s358(s6, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 234
    * Starting at 0xfbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x618

    requires s0.stack[10] == 0x334

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x618;
      assert s1.Peek(10) == 0x334;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push2(s1, 0x0fcb);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0e04);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s359(s8, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xfcb

    requires s0.stack[8] == 0x618

    requires s0.stack[13] == 0x334

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfcb;
      assert s1.Peek(8) == 0x618;
      assert s1.Peek(13) == 0x334;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s360(s5, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xfcb

    requires s0.stack[10] == 0x618

    requires s0.stack[15] == 0x334

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xfcb;
      assert s1.Peek(10) == 0x618;
      assert s1.Peek(15) == 0x334;
      assert s1.Peek(21) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s361(s9, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xfcb

    requires s0.stack[9] == 0x618

    requires s0.stack[14] == 0x334

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfcb;
      assert s1.Peek(9) == 0x618;
      assert s1.Peek(14) == 0x334;
      assert s1.Peek(20) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s6, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 235
    * Starting at 0xfcb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x618

    requires s0.stack[10] == 0x334

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x618;
      assert s1.Peek(10) == 0x334;
      assert s1.Peek(16) == 0x13c;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s8, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 108
    * Starting at 0x618
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x618 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x334

    requires s0.stack[11] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x334;
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

  /** Node 364
    * Segment Id for this node is: 109
    * Starting at 0x621
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x621 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x334

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x334;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push2(s1, 0x062f);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Sub(s6);
      var s8 := Push0(s7);
      var s9 := Push2(s8, 0x0870);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s10, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 129
    * Starting at 0x870
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x870 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x62f

    requires s0.stack[9] == 0x334

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x62f;
      assert s1.Peek(9) == 0x334;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x08e0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s375(s10, gas - 1)
      else
        ExecuteFromCFGNode_s366(s10, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 130
    * Starting at 0x8a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x62f

    requires s0.stack[9] == 0x334

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x62f;
      assert s1.Peek(10) == 0x334;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xe602df0500000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x08d7);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x8d7;
      assert s11.Peek(7) == 0x62f;
      assert s11.Peek(12) == 0x334;
      assert s11.Peek(18) == 0x13c;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s367(s13, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x8d7

    requires s0.stack[7] == 0x62f

    requires s0.stack[12] == 0x334

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8d7;
      assert s1.Peek(7) == 0x62f;
      assert s1.Peek(12) == 0x334;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x8d7;
      assert s11.Peek(10) == 0x62f;
      assert s11.Peek(15) == 0x334;
      assert s11.Peek(21) == 0x13c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s14, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x8d7

    requires s0.stack[11] == 0x62f

    requires s0.stack[16] == 0x334

    requires s0.stack[22] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x8d7;
      assert s1.Peek(11) == 0x62f;
      assert s1.Peek(16) == 0x334;
      assert s1.Peek(22) == 0x13c;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s5, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x8d7

    requires s0.stack[13] == 0x62f

    requires s0.stack[18] == 0x334

    requires s0.stack[24] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x8d7;
      assert s1.Peek(13) == 0x62f;
      assert s1.Peek(18) == 0x334;
      assert s1.Peek(24) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s6, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x8d7

    requires s0.stack[16] == 0x62f

    requires s0.stack[21] == 0x334

    requires s0.stack[27] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x8d7;
      assert s1.Peek(16) == 0x62f;
      assert s1.Peek(21) == 0x334;
      assert s1.Peek(27) == 0x13c;
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
      ExecuteFromCFGNode_s371(s11, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x8d7

    requires s0.stack[15] == 0x62f

    requires s0.stack[20] == 0x334

    requires s0.stack[26] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x8d7;
      assert s1.Peek(15) == 0x62f;
      assert s1.Peek(20) == 0x334;
      assert s1.Peek(26) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s7, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x8d7

    requires s0.stack[12] == 0x62f

    requires s0.stack[17] == 0x334

    requires s0.stack[23] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x8d7;
      assert s1.Peek(12) == 0x62f;
      assert s1.Peek(17) == 0x334;
      assert s1.Peek(23) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s6, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x8d7

    requires s0.stack[8] == 0x62f

    requires s0.stack[13] == 0x334

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8d7;
      assert s1.Peek(8) == 0x62f;
      assert s1.Peek(13) == 0x334;
      assert s1.Peek(19) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s374(s6, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 131
    * Starting at 0x8d7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x62f

    requires s0.stack[10] == 0x334

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x62f;
      assert s1.Peek(10) == 0x334;
      assert s1.Peek(16) == 0x13c;
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

  /** Node 375
    * Segment Id for this node is: 132
    * Starting at 0x8e0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x62f

    requires s0.stack[9] == 0x334

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x62f;
      assert s1.Peek(9) == 0x334;
      assert s1.Peek(15) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0950);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s385(s10, gas - 1)
      else
        ExecuteFromCFGNode_s376(s10, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 133
    * Starting at 0x914
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x914 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x62f

    requires s0.stack[9] == 0x334

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x62f;
      assert s1.Peek(10) == 0x334;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x94280d6200000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0947);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x947;
      assert s11.Peek(7) == 0x62f;
      assert s11.Peek(12) == 0x334;
      assert s11.Peek(18) == 0x13c;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s13, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x947

    requires s0.stack[7] == 0x62f

    requires s0.stack[12] == 0x334

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x947;
      assert s1.Peek(7) == 0x62f;
      assert s1.Peek(12) == 0x334;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x947;
      assert s11.Peek(10) == 0x62f;
      assert s11.Peek(15) == 0x334;
      assert s11.Peek(21) == 0x13c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s378(s14, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x947

    requires s0.stack[11] == 0x62f

    requires s0.stack[16] == 0x334

    requires s0.stack[22] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x947;
      assert s1.Peek(11) == 0x62f;
      assert s1.Peek(16) == 0x334;
      assert s1.Peek(22) == 0x13c;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s379(s5, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x947

    requires s0.stack[13] == 0x62f

    requires s0.stack[18] == 0x334

    requires s0.stack[24] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x947;
      assert s1.Peek(13) == 0x62f;
      assert s1.Peek(18) == 0x334;
      assert s1.Peek(24) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s6, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x947

    requires s0.stack[16] == 0x62f

    requires s0.stack[21] == 0x334

    requires s0.stack[27] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x947;
      assert s1.Peek(16) == 0x62f;
      assert s1.Peek(21) == 0x334;
      assert s1.Peek(27) == 0x13c;
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
      ExecuteFromCFGNode_s381(s11, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x947

    requires s0.stack[15] == 0x62f

    requires s0.stack[20] == 0x334

    requires s0.stack[26] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x947;
      assert s1.Peek(15) == 0x62f;
      assert s1.Peek(20) == 0x334;
      assert s1.Peek(26) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s7, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x947

    requires s0.stack[12] == 0x62f

    requires s0.stack[17] == 0x334

    requires s0.stack[23] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x947;
      assert s1.Peek(12) == 0x62f;
      assert s1.Peek(17) == 0x334;
      assert s1.Peek(23) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s6, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x947

    requires s0.stack[8] == 0x62f

    requires s0.stack[13] == 0x334

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x947;
      assert s1.Peek(8) == 0x62f;
      assert s1.Peek(13) == 0x334;
      assert s1.Peek(19) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s384(s6, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 134
    * Starting at 0x947
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x947 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x62f

    requires s0.stack[10] == 0x334

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x62f;
      assert s1.Peek(10) == 0x334;
      assert s1.Peek(16) == 0x13c;
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

  /** Node 385
    * Segment Id for this node is: 135
    * Starting at 0x950
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x950 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x62f

    requires s0.stack[9] == 0x334

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x62f;
      assert s1.Peek(9) == 0x334;
      assert s1.Peek(15) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup7(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x62f;
      assert s11.Peek(12) == 0x334;
      assert s11.Peek(18) == 0x13c;
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
      assert s21.Peek(7) == 0x62f;
      assert s21.Peek(12) == 0x334;
      assert s21.Peek(18) == 0x13c;
      var s22 := Dup6(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x62f;
      assert s31.Peek(12) == 0x334;
      assert s31.Peek(18) == 0x13c;
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
      ExecuteFromCFGNode_s386(s41, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 136
    * Starting at 0x9ce
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x62f

    requires s0.stack[9] == 0x334

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0x62f;
      assert s1.Peek(10) == 0x334;
      assert s1.Peek(16) == 0x13c;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0a39);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s394(s4, gas - 1)
      else
        ExecuteFromCFGNode_s387(s4, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 137
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x62f

    requires s0.stack[9] == 0x334

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(5) == 0x62f;
      assert s1.Peek(10) == 0x334;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup5(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x0a30);
      assert s11.Peek(0) == 0xa30;
      assert s11.Peek(10) == 0x62f;
      assert s11.Peek(15) == 0x334;
      assert s11.Peek(21) == 0x13c;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0e13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s388(s15, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 196
    * Starting at 0xe13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xa30

    requires s0.stack[10] == 0x62f

    requires s0.stack[15] == 0x334

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa30;
      assert s1.Peek(10) == 0x62f;
      assert s1.Peek(15) == 0x334;
      assert s1.Peek(21) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0e26);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xe26;
      assert s11.Peek(5) == 0xa30;
      assert s11.Peek(13) == 0x62f;
      assert s11.Peek(18) == 0x334;
      assert s11.Peek(24) == 0x13c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e04);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s389(s14, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0xe26

    requires s0.stack[6] == 0xa30

    requires s0.stack[14] == 0x62f

    requires s0.stack[19] == 0x334

    requires s0.stack[25] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe26;
      assert s1.Peek(6) == 0xa30;
      assert s1.Peek(14) == 0x62f;
      assert s1.Peek(19) == 0x334;
      assert s1.Peek(25) == 0x13c;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s390(s5, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xe26

    requires s0.stack[8] == 0xa30

    requires s0.stack[16] == 0x62f

    requires s0.stack[21] == 0x334

    requires s0.stack[27] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xe26;
      assert s1.Peek(8) == 0xa30;
      assert s1.Peek(16) == 0x62f;
      assert s1.Peek(21) == 0x334;
      assert s1.Peek(27) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s391(s9, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0xe26

    requires s0.stack[7] == 0xa30

    requires s0.stack[15] == 0x62f

    requires s0.stack[20] == 0x334

    requires s0.stack[26] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe26;
      assert s1.Peek(7) == 0xa30;
      assert s1.Peek(15) == 0x62f;
      assert s1.Peek(20) == 0x334;
      assert s1.Peek(26) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s392(s6, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 197
    * Starting at 0xe26
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0xa30

    requires s0.stack[11] == 0x62f

    requires s0.stack[16] == 0x334

    requires s0.stack[22] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa30;
      assert s1.Peek(11) == 0x62f;
      assert s1.Peek(16) == 0x334;
      assert s1.Peek(22) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s6, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 138
    * Starting at 0xa30
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0x62f

    requires s0.stack[13] == 0x334

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x62f;
      assert s1.Peek(13) == 0x334;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s394(s8, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 139
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x62f

    requires s0.stack[9] == 0x334

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x62f;
      assert s1.Peek(9) == 0x334;
      assert s1.Peek(15) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s395(s6, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 110
    * Starting at 0x62f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x334

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s396(s1, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 111
    * Starting at 0x630
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x630 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x334

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x334;
      assert s1.Peek(10) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s397(s6, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 73
    * Starting at 0x334
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x334 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x13c;
      var s2 := Push2(s1, 0x033f);
      var s3 := Dup6(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Push2(s5, 0x0636);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s7, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 112
    * Starting at 0x636
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x636 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x33f

    requires s0.stack[9] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33f;
      assert s1.Peek(9) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a6);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s408(s10, gas - 1)
      else
        ExecuteFromCFGNode_s399(s10, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 113
    * Starting at 0x66a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x33f

    requires s0.stack[9] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x33f;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x96c6fd1e00000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x069d);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x69d;
      assert s11.Peek(6) == 0x33f;
      assert s11.Peek(12) == 0x13c;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s400(s13, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x69d

    requires s0.stack[6] == 0x33f

    requires s0.stack[12] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x69d;
      assert s1.Peek(6) == 0x33f;
      assert s1.Peek(12) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x69d;
      assert s11.Peek(9) == 0x33f;
      assert s11.Peek(15) == 0x13c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s401(s14, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x69d

    requires s0.stack[10] == 0x33f

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x69d;
      assert s1.Peek(10) == 0x33f;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s402(s5, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x69d

    requires s0.stack[12] == 0x33f

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x69d;
      assert s1.Peek(12) == 0x33f;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s403(s6, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x69d

    requires s0.stack[15] == 0x33f

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x69d;
      assert s1.Peek(15) == 0x33f;
      assert s1.Peek(21) == 0x13c;
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
      ExecuteFromCFGNode_s404(s11, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x69d

    requires s0.stack[14] == 0x33f

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x69d;
      assert s1.Peek(14) == 0x33f;
      assert s1.Peek(20) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s7, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x69d

    requires s0.stack[11] == 0x33f

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x69d;
      assert s1.Peek(11) == 0x33f;
      assert s1.Peek(17) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s6, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x69d

    requires s0.stack[7] == 0x33f

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x69d;
      assert s1.Peek(7) == 0x33f;
      assert s1.Peek(13) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s407(s6, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 114
    * Starting at 0x69d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x33f

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x33f;
      assert s1.Peek(10) == 0x13c;
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

  /** Node 408
    * Segment Id for this node is: 115
    * Starting at 0x6a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x33f

    requires s0.stack[9] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33f;
      assert s1.Peek(9) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0716);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s418(s10, gas - 1)
      else
        ExecuteFromCFGNode_s409(s10, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 116
    * Starting at 0x6da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x33f

    requires s0.stack[9] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x33f;
      assert s1.Peek(10) == 0x13c;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xec442f0500000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x070d);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x70d;
      assert s11.Peek(6) == 0x33f;
      assert s11.Peek(12) == 0x13c;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s410(s13, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x70d

    requires s0.stack[6] == 0x33f

    requires s0.stack[12] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x70d;
      assert s1.Peek(6) == 0x33f;
      assert s1.Peek(12) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x70d;
      assert s11.Peek(9) == 0x33f;
      assert s11.Peek(15) == 0x13c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s411(s14, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x70d

    requires s0.stack[10] == 0x33f

    requires s0.stack[16] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x70d;
      assert s1.Peek(10) == 0x33f;
      assert s1.Peek(16) == 0x13c;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s412(s5, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x70d

    requires s0.stack[12] == 0x33f

    requires s0.stack[18] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x70d;
      assert s1.Peek(12) == 0x33f;
      assert s1.Peek(18) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s413(s6, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x70d

    requires s0.stack[15] == 0x33f

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x70d;
      assert s1.Peek(15) == 0x33f;
      assert s1.Peek(21) == 0x13c;
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
      ExecuteFromCFGNode_s414(s11, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x70d

    requires s0.stack[14] == 0x33f

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x70d;
      assert s1.Peek(14) == 0x33f;
      assert s1.Peek(20) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s7, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x70d

    requires s0.stack[11] == 0x33f

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x70d;
      assert s1.Peek(11) == 0x33f;
      assert s1.Peek(17) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s416(s6, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x70d

    requires s0.stack[7] == 0x33f

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x70d;
      assert s1.Peek(7) == 0x33f;
      assert s1.Peek(13) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s417(s6, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 117
    * Starting at 0x70d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x33f

    requires s0.stack[10] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x33f;
      assert s1.Peek(10) == 0x13c;
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

  /** Node 418
    * Segment Id for this node is: 118
    * Starting at 0x716
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x716 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x33f

    requires s0.stack[9] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33f;
      assert s1.Peek(9) == 0x13c;
      var s2 := Push2(s1, 0x0721);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0a3f);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s419(s7, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 140
    * Starting at 0xa3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x33f

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x721;
      assert s1.Peek(7) == 0x33f;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0a8f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s449(s10, gas - 1)
      else
        ExecuteFromCFGNode_s420(s10, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 141
    * Starting at 0xa73
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x33f

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x721;
      assert s1.Peek(8) == 0x33f;
      assert s1.Peek(14) == 0x13c;
      var s2 := Push1(s1, 0x02);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := SLoad(s5);
      var s7 := Push2(s6, 0x0a83);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1000);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s11, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 237
    * Starting at 0x1000
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1000 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xa83

    requires s0.stack[9] == 0x721

    requires s0.stack[13] == 0x33f

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa83;
      assert s1.Peek(9) == 0x721;
      assert s1.Peek(13) == 0x33f;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x100a);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d60);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s422(s6, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x100a

    requires s0.stack[5] == 0xa83

    requires s0.stack[12] == 0x721

    requires s0.stack[16] == 0x33f

    requires s0.stack[22] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x100a;
      assert s1.Peek(5) == 0xa83;
      assert s1.Peek(12) == 0x721;
      assert s1.Peek(16) == 0x33f;
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
      ExecuteFromCFGNode_s423(s9, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 238
    * Starting at 0x100a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[4] == 0xa83

    requires s0.stack[11] == 0x721

    requires s0.stack[15] == 0x33f

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa83;
      assert s1.Peek(11) == 0x721;
      assert s1.Peek(15) == 0x33f;
      assert s1.Peek(21) == 0x13c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1015);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0d60);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s424(s7, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0x1015

    requires s0.stack[5] == 0xa83

    requires s0.stack[12] == 0x721

    requires s0.stack[16] == 0x33f

    requires s0.stack[22] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1015;
      assert s1.Peek(5) == 0xa83;
      assert s1.Peek(12) == 0x721;
      assert s1.Peek(16) == 0x33f;
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
      ExecuteFromCFGNode_s425(s9, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 239
    * Starting at 0x1015
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[4] == 0xa83

    requires s0.stack[11] == 0x721

    requires s0.stack[15] == 0x33f

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa83;
      assert s1.Peek(11) == 0x721;
      assert s1.Peek(15) == 0x33f;
      assert s1.Peek(21) == 0x13c;
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
      assert s11.Peek(4) == 0xa83;
      assert s11.Peek(11) == 0x721;
      assert s11.Peek(15) == 0x33f;
      assert s11.Peek(21) == 0x13c;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x102d);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s428(s14, gas - 1)
      else
        ExecuteFromCFGNode_s426(s14, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 240
    * Starting at 0x1025
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1025 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xa83

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x33f

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x102c);
      assert s1.Peek(0) == 0x102c;
      assert s1.Peek(4) == 0xa83;
      assert s1.Peek(11) == 0x721;
      assert s1.Peek(15) == 0x33f;
      assert s1.Peek(21) == 0x13c;
      var s2 := Push2(s1, 0x0fd3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s427(s3, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 236
    * Starting at 0xfd3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x102c

    requires s0.stack[4] == 0xa83

    requires s0.stack[11] == 0x721

    requires s0.stack[15] == 0x33f

    requires s0.stack[21] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x102c;
      assert s1.Peek(4) == 0xa83;
      assert s1.Peek(11) == 0x721;
      assert s1.Peek(15) == 0x33f;
      assert s1.Peek(21) == 0x13c;
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

  /** Node 428
    * Segment Id for this node is: 242
    * Starting at 0x102d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xa83

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x33f

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa83;
      assert s1.Peek(10) == 0x721;
      assert s1.Peek(14) == 0x33f;
      assert s1.Peek(20) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s429(s6, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 142
    * Starting at 0xa83
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x721

    requires s0.stack[11] == 0x33f

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x721;
      assert s1.Peek(11) == 0x33f;
      assert s1.Peek(17) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Push2(s8, 0x0b5d);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s430(s10, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 147
    * Starting at 0xb5d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x33f

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x721;
      assert s1.Peek(7) == 0x33f;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0ba4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s448(s10, gas - 1)
      else
        ExecuteFromCFGNode_s431(s10, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 148
    * Starting at 0xb91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x33f

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x721;
      assert s1.Peek(8) == 0x33f;
      assert s1.Peek(14) == 0x13c;
      var s2 := Push1(s1, 0x02);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := SLoad(s5);
      var s7 := Sub(s6);
      var s8 := Swap3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x721;
      assert s11.Peek(10) == 0x33f;
      assert s11.Peek(16) == 0x13c;
      var s12 := Swap1(s11);
      var s13 := SStore(s12);
      var s14 := Pop(s13);
      var s15 := Push2(s14, 0x0bee);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s432(s16, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 150
    * Starting at 0xbee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x33f

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x721;
      assert s1.Peek(7) == 0x33f;
      assert s1.Peek(13) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push32(s7, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s9 := Dup4(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(8) == 0x721;
      assert s11.Peek(12) == 0x33f;
      assert s11.Peek(18) == 0x13c;
      var s12 := Push2(s11, 0x0c4b);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x0e13);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s433(s16, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 196
    * Starting at 0xe13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xc4b

    requires s0.stack[9] == 0x721

    requires s0.stack[13] == 0x33f

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc4b;
      assert s1.Peek(9) == 0x721;
      assert s1.Peek(13) == 0x33f;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0e26);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xe26;
      assert s11.Peek(5) == 0xc4b;
      assert s11.Peek(12) == 0x721;
      assert s11.Peek(16) == 0x33f;
      assert s11.Peek(22) == 0x13c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e04);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s434(s14, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xe26

    requires s0.stack[6] == 0xc4b

    requires s0.stack[13] == 0x721

    requires s0.stack[17] == 0x33f

    requires s0.stack[23] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe26;
      assert s1.Peek(6) == 0xc4b;
      assert s1.Peek(13) == 0x721;
      assert s1.Peek(17) == 0x33f;
      assert s1.Peek(23) == 0x13c;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s435(s5, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xe26

    requires s0.stack[8] == 0xc4b

    requires s0.stack[15] == 0x721

    requires s0.stack[19] == 0x33f

    requires s0.stack[25] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xe26;
      assert s1.Peek(8) == 0xc4b;
      assert s1.Peek(15) == 0x721;
      assert s1.Peek(19) == 0x33f;
      assert s1.Peek(25) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s436(s9, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xe26

    requires s0.stack[7] == 0xc4b

    requires s0.stack[14] == 0x721

    requires s0.stack[18] == 0x33f

    requires s0.stack[24] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe26;
      assert s1.Peek(7) == 0xc4b;
      assert s1.Peek(14) == 0x721;
      assert s1.Peek(18) == 0x33f;
      assert s1.Peek(24) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s437(s6, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 197
    * Starting at 0xe26
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xc4b

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x33f

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc4b;
      assert s1.Peek(10) == 0x721;
      assert s1.Peek(14) == 0x33f;
      assert s1.Peek(20) == 0x13c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s438(s6, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 151
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x721

    requires s0.stack[11] == 0x33f

    requires s0.stack[17] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x721;
      assert s1.Peek(11) == 0x33f;
      assert s1.Peek(17) == 0x13c;
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
      assert s11.Peek(0) == 0x721;
      assert s11.Peek(4) == 0x33f;
      assert s11.Peek(10) == 0x13c;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s12, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 119
    * Starting at 0x721
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x721 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x33f

    requires s0.stack[9] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33f;
      assert s1.Peek(9) == 0x13c;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s440(s5, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 74
    * Starting at 0x33f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33f as nat
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
      ExecuteFromCFGNode_s441(s11, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 30
    * Starting at 0x13c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
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
      var s7 := Push2(s6, 0x0deb);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s8, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 192
    * Starting at 0xdeb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdeb as nat
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
      var s8 := Push2(s7, 0x0dfe);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xdfe;
      assert s11.Peek(5) == 0x149;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0ddc);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s14, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 190
    * Starting at 0xddc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xddc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0x149

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0x149;
      var s2 := Push2(s1, 0x0de5);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dd1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s444(s5, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 189
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xde5

    requires s0.stack[4] == 0xdfe

    requires s0.stack[8] == 0x149

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde5;
      assert s1.Peek(4) == 0xdfe;
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
      ExecuteFromCFGNode_s445(s11, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 191
    * Starting at 0xde5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0x149

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0x149;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s6, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 193
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
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
      ExecuteFromCFGNode_s447(s6, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 31
    * Starting at 0x149
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
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

  /** Node 448
    * Segment Id for this node is: 149
    * Starting at 0xba4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x33f

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x721;
      assert s1.Peek(7) == 0x33f;
      assert s1.Peek(13) == 0x13c;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Dup1(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x721;
      assert s11.Peek(10) == 0x33f;
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
      assert s21.Peek(6) == 0x721;
      assert s21.Peek(10) == 0x33f;
      assert s21.Peek(16) == 0x13c;
      var s22 := Dup3(s21);
      var s23 := Dup3(s22);
      var s24 := SLoad(s23);
      var s25 := Add(s24);
      var s26 := Swap3(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := SStore(s30);
      assert s31.Peek(4) == 0x721;
      assert s31.Peek(8) == 0x33f;
      assert s31.Peek(14) == 0x13c;
      var s32 := Pop(s31);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s432(s32, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 143
    * Starting at 0xa8f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x721

    requires s0.stack[7] == 0x33f

    requires s0.stack[13] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x721;
      assert s1.Peek(7) == 0x33f;
      assert s1.Peek(13) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x721;
      assert s11.Peek(10) == 0x33f;
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
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x721;
      assert s21.Peek(9) == 0x33f;
      assert s21.Peek(15) == 0x13c;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0b18);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s467(s29, gas - 1)
      else
        ExecuteFromCFGNode_s450(s29, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 144
    * Starting at 0xad8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x721

    requires s0.stack[8] == 0x33f

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(5) == 0x721;
      assert s1.Peek(9) == 0x33f;
      assert s1.Peek(15) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xe450d38c00000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0b0f);
      assert s11.Peek(0) == 0xb0f;
      assert s11.Peek(9) == 0x721;
      assert s11.Peek(13) == 0x33f;
      assert s11.Peek(19) == 0x13c;
      var s12 := Swap4(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Push2(s15, 0x0f9e);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s451(s17, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 232
    * Starting at 0xf9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xb0f

    requires s0.stack[9] == 0x721

    requires s0.stack[13] == 0x33f

    requires s0.stack[19] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb0f;
      assert s1.Peek(9) == 0x721;
      assert s1.Peek(13) == 0x33f;
      assert s1.Peek(19) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0fb1);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xfb1;
      assert s11.Peek(7) == 0xb0f;
      assert s11.Peek(12) == 0x721;
      assert s11.Peek(16) == 0x33f;
      assert s11.Peek(22) == 0x13c;
      var s12 := Dup7(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s14, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xfb1

    requires s0.stack[8] == 0xb0f

    requires s0.stack[13] == 0x721

    requires s0.stack[17] == 0x33f

    requires s0.stack[23] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfb1;
      assert s1.Peek(8) == 0xb0f;
      assert s1.Peek(13) == 0x721;
      assert s1.Peek(17) == 0x33f;
      assert s1.Peek(23) == 0x13c;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s453(s5, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xfb1

    requires s0.stack[10] == 0xb0f

    requires s0.stack[15] == 0x721

    requires s0.stack[19] == 0x33f

    requires s0.stack[25] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xfb1;
      assert s1.Peek(10) == 0xb0f;
      assert s1.Peek(15) == 0x721;
      assert s1.Peek(19) == 0x33f;
      assert s1.Peek(25) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s454(s6, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xfb1

    requires s0.stack[13] == 0xb0f

    requires s0.stack[18] == 0x721

    requires s0.stack[22] == 0x33f

    requires s0.stack[28] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xfb1;
      assert s1.Peek(13) == 0xb0f;
      assert s1.Peek(18) == 0x721;
      assert s1.Peek(22) == 0x33f;
      assert s1.Peek(28) == 0x13c;
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
      ExecuteFromCFGNode_s455(s11, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xfb1

    requires s0.stack[12] == 0xb0f

    requires s0.stack[17] == 0x721

    requires s0.stack[21] == 0x33f

    requires s0.stack[27] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xfb1;
      assert s1.Peek(12) == 0xb0f;
      assert s1.Peek(17) == 0x721;
      assert s1.Peek(21) == 0x33f;
      assert s1.Peek(27) == 0x13c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s456(s7, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xfb1

    requires s0.stack[9] == 0xb0f

    requires s0.stack[14] == 0x721

    requires s0.stack[18] == 0x33f

    requires s0.stack[24] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfb1;
      assert s1.Peek(9) == 0xb0f;
      assert s1.Peek(14) == 0x721;
      assert s1.Peek(18) == 0x33f;
      assert s1.Peek(24) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s457(s6, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 233
    * Starting at 0xfb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xb0f

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x33f

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xb0f;
      assert s1.Peek(10) == 0x721;
      assert s1.Peek(14) == 0x33f;
      assert s1.Peek(20) == 0x13c;
      var s2 := Push2(s1, 0x0fbe);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup6(s5);
      var s7 := Push2(s6, 0x0e04);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s458(s8, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xfbe

    requires s0.stack[8] == 0xb0f

    requires s0.stack[13] == 0x721

    requires s0.stack[17] == 0x33f

    requires s0.stack[23] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfbe;
      assert s1.Peek(8) == 0xb0f;
      assert s1.Peek(13) == 0x721;
      assert s1.Peek(17) == 0x33f;
      assert s1.Peek(23) == 0x13c;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s5, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xfbe

    requires s0.stack[10] == 0xb0f

    requires s0.stack[15] == 0x721

    requires s0.stack[19] == 0x33f

    requires s0.stack[25] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xfbe;
      assert s1.Peek(10) == 0xb0f;
      assert s1.Peek(15) == 0x721;
      assert s1.Peek(19) == 0x33f;
      assert s1.Peek(25) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s9, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xfbe

    requires s0.stack[9] == 0xb0f

    requires s0.stack[14] == 0x721

    requires s0.stack[18] == 0x33f

    requires s0.stack[24] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfbe;
      assert s1.Peek(9) == 0xb0f;
      assert s1.Peek(14) == 0x721;
      assert s1.Peek(18) == 0x33f;
      assert s1.Peek(24) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s6, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 234
    * Starting at 0xfbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xb0f

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x33f

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xb0f;
      assert s1.Peek(10) == 0x721;
      assert s1.Peek(14) == 0x33f;
      assert s1.Peek(20) == 0x13c;
      var s2 := Push2(s1, 0x0fcb);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0e04);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s8, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xfcb

    requires s0.stack[8] == 0xb0f

    requires s0.stack[13] == 0x721

    requires s0.stack[17] == 0x33f

    requires s0.stack[23] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfcb;
      assert s1.Peek(8) == 0xb0f;
      assert s1.Peek(13) == 0x721;
      assert s1.Peek(17) == 0x33f;
      assert s1.Peek(23) == 0x13c;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s463(s5, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xfcb

    requires s0.stack[10] == 0xb0f

    requires s0.stack[15] == 0x721

    requires s0.stack[19] == 0x33f

    requires s0.stack[25] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xfcb;
      assert s1.Peek(10) == 0xb0f;
      assert s1.Peek(15) == 0x721;
      assert s1.Peek(19) == 0x33f;
      assert s1.Peek(25) == 0x13c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s9, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xfcb

    requires s0.stack[9] == 0xb0f

    requires s0.stack[14] == 0x721

    requires s0.stack[18] == 0x33f

    requires s0.stack[24] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfcb;
      assert s1.Peek(9) == 0xb0f;
      assert s1.Peek(14) == 0x721;
      assert s1.Peek(18) == 0x33f;
      assert s1.Peek(24) == 0x13c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s465(s6, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 235
    * Starting at 0xfcb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xb0f

    requires s0.stack[10] == 0x721

    requires s0.stack[14] == 0x33f

    requires s0.stack[20] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xb0f;
      assert s1.Peek(10) == 0x721;
      assert s1.Peek(14) == 0x33f;
      assert s1.Peek(20) == 0x13c;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s466(s8, gas - 1)
  }

  /** Node 466
    * Segment Id for this node is: 145
    * Starting at 0xb0f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x721

    requires s0.stack[9] == 0x33f

    requires s0.stack[15] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x721;
      assert s1.Peek(9) == 0x33f;
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
    * Segment Id for this node is: 146
    * Starting at 0xb18
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x721

    requires s0.stack[8] == 0x33f

    requires s0.stack[14] == 0x13c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x721;
      assert s1.Peek(8) == 0x33f;
      assert s1.Peek(14) == 0x13c;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push0(s4);
      var s6 := Dup1(s5);
      var s7 := Dup7(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x721;
      assert s11.Peek(12) == 0x33f;
      assert s11.Peek(18) == 0x13c;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push0(s20);
      assert s21.Peek(7) == 0x721;
      assert s21.Peek(11) == 0x33f;
      assert s21.Peek(17) == 0x13c;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s430(s27, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 25
    * Starting at 0x104
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push2(s2, 0x0314);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s4, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 70
    * Starting at 0x314
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x314 as nat
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
      var s3 := Push1(s2, 0x02);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s470(s8, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 26
    * Starting at 0x10c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
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
      var s7 := Push2(s6, 0x0e13);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s471(s8, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 196
    * Starting at 0xe13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe13 as nat
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
      var s8 := Push2(s7, 0x0e26);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xe26;
      assert s11.Peek(5) == 0x119;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e04);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s14, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xe26

    requires s0.stack[6] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe26;
      assert s1.Peek(6) == 0x119;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s473(s5, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xe26

    requires s0.stack[8] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xe26;
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
      ExecuteFromCFGNode_s474(s9, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xe26

    requires s0.stack[7] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe26;
      assert s1.Peek(7) == 0x119;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s475(s6, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 197
    * Starting at 0xe26
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe26 as nat
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
      ExecuteFromCFGNode_s476(s6, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 27
    * Starting at 0x119
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
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

  /** Node 477
    * Segment Id for this node is: 21
    * Starting at 0xd4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
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
      var s13 := Push2(s12, 0x0d93);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s478(s14, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 183
    * Starting at 0xd93
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd93 as nat
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
      var s10 := Push2(s9, 0x0da9);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s481(s11, gas - 1)
      else
        ExecuteFromCFGNode_s479(s11, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 184
    * Starting at 0xda1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xe9

    requires s0.stack[5] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0da8);
      assert s1.Peek(0) == 0xda8;
      assert s1.Peek(5) == 0xe9;
      assert s1.Peek(6) == 0xee;
      var s2 := Push2(s1, 0x0d02);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s480(s3, gas - 1)
  }

  /** Node 480
    * Segment Id for this node is: 166
    * Starting at 0xd02
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xda8

    requires s0.stack[5] == 0xe9

    requires s0.stack[6] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xda8;
      assert s1.Peek(5) == 0xe9;
      assert s1.Peek(6) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 481
    * Segment Id for this node is: 186
    * Starting at 0xda9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda9 as nat
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
      var s3 := Push2(s2, 0x0db6);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0d4c);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s9, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 174
    * Starting at 0xd4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xdb6

    requires s0.stack[8] == 0xe9

    requires s0.stack[9] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb6;
      assert s1.Peek(8) == 0xe9;
      assert s1.Peek(9) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d5a);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d36);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s483(s10, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 170
    * Starting at 0xd36
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xdb6

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xdb6;
      assert s1.Peek(11) == 0xe9;
      assert s1.Peek(12) == 0xee;
      var s2 := Push2(s1, 0x0d3f);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s484(s5, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xd3f

    requires s0.stack[3] == 0xd5a

    requires s0.stack[7] == 0xdb6

    requires s0.stack[13] == 0xe9

    requires s0.stack[14] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd3f;
      assert s1.Peek(3) == 0xd5a;
      assert s1.Peek(7) == 0xdb6;
      assert s1.Peek(13) == 0xe9;
      assert s1.Peek(14) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s6, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xd3f

    requires s0.stack[6] == 0xd5a

    requires s0.stack[10] == 0xdb6

    requires s0.stack[16] == 0xe9

    requires s0.stack[17] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xd3f;
      assert s1.Peek(6) == 0xd5a;
      assert s1.Peek(10) == 0xdb6;
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
      ExecuteFromCFGNode_s486(s11, gas - 1)
  }

  /** Node 486
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xd3f

    requires s0.stack[5] == 0xd5a

    requires s0.stack[9] == 0xdb6

    requires s0.stack[15] == 0xe9

    requires s0.stack[16] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3f;
      assert s1.Peek(5) == 0xd5a;
      assert s1.Peek(9) == 0xdb6;
      assert s1.Peek(15) == 0xe9;
      assert s1.Peek(16) == 0xee;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s487(s7, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 171
    * Starting at 0xd3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd5a

    requires s0.stack[6] == 0xdb6

    requires s0.stack[12] == 0xe9

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xdb6;
      assert s1.Peek(12) == 0xe9;
      assert s1.Peek(13) == 0xee;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d49);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s489(s5, gas - 1)
      else
        ExecuteFromCFGNode_s488(s5, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 172
    * Starting at 0xd46
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xdb6

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd5a;
      assert s1.Peek(6) == 0xdb6;
      assert s1.Peek(12) == 0xe9;
      assert s1.Peek(13) == 0xee;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 489
    * Segment Id for this node is: 173
    * Starting at 0xd49
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd5a

    requires s0.stack[5] == 0xdb6

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd5a;
      assert s1.Peek(5) == 0xdb6;
      assert s1.Peek(11) == 0xe9;
      assert s1.Peek(12) == 0xee;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s490(s3, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 175
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xdb6

    requires s0.stack[9] == 0xe9

    requires s0.stack[10] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb6;
      assert s1.Peek(9) == 0xe9;
      assert s1.Peek(10) == 0xee;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s6, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 187
    * Starting at 0xdb6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb6 as nat
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
      var s6 := Push2(s5, 0x0dc7);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d7f);
      assert s11.Peek(0) == 0xd7f;
      assert s11.Peek(3) == 0xdc7;
      assert s11.Peek(9) == 0xe9;
      assert s11.Peek(10) == 0xee;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s492(s12, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 181
    * Starting at 0xd7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xdc7

    requires s0.stack[8] == 0xe9

    requires s0.stack[9] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdc7;
      assert s1.Peek(8) == 0xe9;
      assert s1.Peek(9) == 0xee;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0d8d);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0d69);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s493(s10, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 177
    * Starting at 0xd69
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd8d

    requires s0.stack[5] == 0xdc7

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd8d;
      assert s1.Peek(5) == 0xdc7;
      assert s1.Peek(11) == 0xe9;
      assert s1.Peek(12) == 0xee;
      var s2 := Push2(s1, 0x0d72);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s494(s5, gas - 1)
  }

  /** Node 494
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xd72

    requires s0.stack[3] == 0xd8d

    requires s0.stack[7] == 0xdc7

    requires s0.stack[13] == 0xe9

    requires s0.stack[14] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd72;
      assert s1.Peek(3) == 0xd8d;
      assert s1.Peek(7) == 0xdc7;
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
      ExecuteFromCFGNode_s495(s9, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 178
    * Starting at 0xd72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xd8d

    requires s0.stack[6] == 0xdc7

    requires s0.stack[12] == 0xe9

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd8d;
      assert s1.Peek(6) == 0xdc7;
      assert s1.Peek(12) == 0xe9;
      assert s1.Peek(13) == 0xee;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0d7c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s497(s5, gas - 1)
      else
        ExecuteFromCFGNode_s496(s5, gas - 1)
  }

  /** Node 496
    * Segment Id for this node is: 179
    * Starting at 0xd79
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd8d

    requires s0.stack[5] == 0xdc7

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xd8d;
      assert s1.Peek(6) == 0xdc7;
      assert s1.Peek(12) == 0xe9;
      assert s1.Peek(13) == 0xee;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 497
    * Segment Id for this node is: 180
    * Starting at 0xd7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd8d

    requires s0.stack[5] == 0xdc7

    requires s0.stack[11] == 0xe9

    requires s0.stack[12] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd8d;
      assert s1.Peek(5) == 0xdc7;
      assert s1.Peek(11) == 0xe9;
      assert s1.Peek(12) == 0xee;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s3, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 182
    * Starting at 0xd8d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xdc7

    requires s0.stack[9] == 0xe9

    requires s0.stack[10] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdc7;
      assert s1.Peek(9) == 0xe9;
      assert s1.Peek(10) == 0xee;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s6, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 188
    * Starting at 0xdc7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc7 as nat
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
      ExecuteFromCFGNode_s500(s10, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 22
    * Starting at 0xe9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
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
      var s2 := Push2(s1, 0x02f2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s501(s3, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 67
    * Starting at 0x2f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f2 as nat
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
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x02fc);
      var s5 := Push2(s4, 0x058b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s502(s6, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 101
    * Starting at 0x58b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x2fc

    requires s0.stack[5] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2fc;
      assert s1.Peek(5) == 0xee;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s503(s7, gas - 1)
  }

  /** Node 503
    * Segment Id for this node is: 68
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xee;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0309);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x0592);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s504(s9, gas - 1)
  }

  /** Node 504
    * Segment Id for this node is: 102
    * Starting at 0x592
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x592 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x309

    requires s0.stack[8] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x309;
      assert s1.Peek(8) == 0xee;
      var s2 := Push2(s1, 0x059f);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push2(s6, 0x0870);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s505(s8, gas - 1)
  }

  /** Node 505
    * Segment Id for this node is: 129
    * Starting at 0x870
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x870 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x59f

    requires s0.stack[8] == 0x309

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x59f;
      assert s1.Peek(8) == 0x309;
      assert s1.Peek(13) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x08e0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s515(s10, gas - 1)
      else
        ExecuteFromCFGNode_s506(s10, gas - 1)
  }

  /** Node 506
    * Segment Id for this node is: 130
    * Starting at 0x8a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x59f

    requires s0.stack[8] == 0x309

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x59f;
      assert s1.Peek(9) == 0x309;
      assert s1.Peek(14) == 0xee;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xe602df0500000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x08d7);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x8d7;
      assert s11.Peek(7) == 0x59f;
      assert s11.Peek(11) == 0x309;
      assert s11.Peek(16) == 0xee;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s507(s13, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x8d7

    requires s0.stack[7] == 0x59f

    requires s0.stack[11] == 0x309

    requires s0.stack[16] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8d7;
      assert s1.Peek(7) == 0x59f;
      assert s1.Peek(11) == 0x309;
      assert s1.Peek(16) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x8d7;
      assert s11.Peek(10) == 0x59f;
      assert s11.Peek(14) == 0x309;
      assert s11.Peek(19) == 0xee;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s508(s14, gas - 1)
  }

  /** Node 508
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x8d7

    requires s0.stack[11] == 0x59f

    requires s0.stack[15] == 0x309

    requires s0.stack[20] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x8d7;
      assert s1.Peek(11) == 0x59f;
      assert s1.Peek(15) == 0x309;
      assert s1.Peek(20) == 0xee;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s509(s5, gas - 1)
  }

  /** Node 509
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x8d7

    requires s0.stack[13] == 0x59f

    requires s0.stack[17] == 0x309

    requires s0.stack[22] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x8d7;
      assert s1.Peek(13) == 0x59f;
      assert s1.Peek(17) == 0x309;
      assert s1.Peek(22) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s510(s6, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x8d7

    requires s0.stack[16] == 0x59f

    requires s0.stack[20] == 0x309

    requires s0.stack[25] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x8d7;
      assert s1.Peek(16) == 0x59f;
      assert s1.Peek(20) == 0x309;
      assert s1.Peek(25) == 0xee;
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
      ExecuteFromCFGNode_s511(s11, gas - 1)
  }

  /** Node 511
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x8d7

    requires s0.stack[15] == 0x59f

    requires s0.stack[19] == 0x309

    requires s0.stack[24] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x8d7;
      assert s1.Peek(15) == 0x59f;
      assert s1.Peek(19) == 0x309;
      assert s1.Peek(24) == 0xee;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s512(s7, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x8d7

    requires s0.stack[12] == 0x59f

    requires s0.stack[16] == 0x309

    requires s0.stack[21] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x8d7;
      assert s1.Peek(12) == 0x59f;
      assert s1.Peek(16) == 0x309;
      assert s1.Peek(21) == 0xee;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s6, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x8d7

    requires s0.stack[8] == 0x59f

    requires s0.stack[12] == 0x309

    requires s0.stack[17] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8d7;
      assert s1.Peek(8) == 0x59f;
      assert s1.Peek(12) == 0x309;
      assert s1.Peek(17) == 0xee;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s514(s6, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 131
    * Starting at 0x8d7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x59f

    requires s0.stack[9] == 0x309

    requires s0.stack[14] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x59f;
      assert s1.Peek(9) == 0x309;
      assert s1.Peek(14) == 0xee;
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

  /** Node 515
    * Segment Id for this node is: 132
    * Starting at 0x8e0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x59f

    requires s0.stack[8] == 0x309

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x59f;
      assert s1.Peek(8) == 0x309;
      assert s1.Peek(13) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0950);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s525(s10, gas - 1)
      else
        ExecuteFromCFGNode_s516(s10, gas - 1)
  }

  /** Node 516
    * Segment Id for this node is: 133
    * Starting at 0x914
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x914 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x59f

    requires s0.stack[8] == 0x309

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x59f;
      assert s1.Peek(9) == 0x309;
      assert s1.Peek(14) == 0xee;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x94280d6200000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0947);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x947;
      assert s11.Peek(7) == 0x59f;
      assert s11.Peek(11) == 0x309;
      assert s11.Peek(16) == 0xee;
      var s12 := Push2(s11, 0x0eea);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s517(s13, gas - 1)
  }

  /** Node 517
    * Segment Id for this node is: 217
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x947

    requires s0.stack[7] == 0x59f

    requires s0.stack[11] == 0x309

    requires s0.stack[16] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x947;
      assert s1.Peek(7) == 0x59f;
      assert s1.Peek(11) == 0x309;
      assert s1.Peek(16) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0efd);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xefd;
      assert s11.Peek(5) == 0x947;
      assert s11.Peek(10) == 0x59f;
      assert s11.Peek(14) == 0x309;
      assert s11.Peek(19) == 0xee;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0edb);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s518(s14, gas - 1)
  }

  /** Node 518
    * Segment Id for this node is: 215
    * Starting at 0xedb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xefd

    requires s0.stack[6] == 0x947

    requires s0.stack[11] == 0x59f

    requires s0.stack[15] == 0x309

    requires s0.stack[20] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xefd;
      assert s1.Peek(6) == 0x947;
      assert s1.Peek(11) == 0x59f;
      assert s1.Peek(15) == 0x309;
      assert s1.Peek(20) == 0xee;
      var s2 := Push2(s1, 0x0ee4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d25);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s519(s5, gas - 1)
  }

  /** Node 519
    * Segment Id for this node is: 168
    * Starting at 0xd25
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0xee4

    requires s0.stack[4] == 0xefd

    requires s0.stack[8] == 0x947

    requires s0.stack[13] == 0x59f

    requires s0.stack[17] == 0x309

    requires s0.stack[22] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xee4;
      assert s1.Peek(4) == 0xefd;
      assert s1.Peek(8) == 0x947;
      assert s1.Peek(13) == 0x59f;
      assert s1.Peek(17) == 0x309;
      assert s1.Peek(22) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d2f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0d06);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s520(s6, gas - 1)
  }

  /** Node 520
    * Segment Id for this node is: 167
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0xd2f

    requires s0.stack[4] == 0xee4

    requires s0.stack[7] == 0xefd

    requires s0.stack[11] == 0x947

    requires s0.stack[16] == 0x59f

    requires s0.stack[20] == 0x309

    requires s0.stack[25] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2f;
      assert s1.Peek(4) == 0xee4;
      assert s1.Peek(7) == 0xefd;
      assert s1.Peek(11) == 0x947;
      assert s1.Peek(16) == 0x59f;
      assert s1.Peek(20) == 0x309;
      assert s1.Peek(25) == 0xee;
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
      ExecuteFromCFGNode_s521(s11, gas - 1)
  }

  /** Node 521
    * Segment Id for this node is: 169
    * Starting at 0xd2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xee4

    requires s0.stack[6] == 0xefd

    requires s0.stack[10] == 0x947

    requires s0.stack[15] == 0x59f

    requires s0.stack[19] == 0x309

    requires s0.stack[24] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee4;
      assert s1.Peek(6) == 0xefd;
      assert s1.Peek(10) == 0x947;
      assert s1.Peek(15) == 0x59f;
      assert s1.Peek(19) == 0x309;
      assert s1.Peek(24) == 0xee;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s522(s7, gas - 1)
  }

  /** Node 522
    * Segment Id for this node is: 216
    * Starting at 0xee4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xefd

    requires s0.stack[7] == 0x947

    requires s0.stack[12] == 0x59f

    requires s0.stack[16] == 0x309

    requires s0.stack[21] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xefd;
      assert s1.Peek(7) == 0x947;
      assert s1.Peek(12) == 0x59f;
      assert s1.Peek(16) == 0x309;
      assert s1.Peek(21) == 0xee;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s523(s6, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 218
    * Starting at 0xefd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x947

    requires s0.stack[8] == 0x59f

    requires s0.stack[12] == 0x309

    requires s0.stack[17] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x947;
      assert s1.Peek(8) == 0x59f;
      assert s1.Peek(12) == 0x309;
      assert s1.Peek(17) == 0xee;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s524(s6, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 134
    * Starting at 0x947
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x947 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x59f

    requires s0.stack[9] == 0x309

    requires s0.stack[14] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x59f;
      assert s1.Peek(9) == 0x309;
      assert s1.Peek(14) == 0xee;
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

  /** Node 525
    * Segment Id for this node is: 135
    * Starting at 0x950
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x950 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x59f

    requires s0.stack[8] == 0x309

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x59f;
      assert s1.Peek(8) == 0x309;
      assert s1.Peek(13) == 0xee;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup7(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x59f;
      assert s11.Peek(11) == 0x309;
      assert s11.Peek(16) == 0xee;
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
      assert s21.Peek(7) == 0x59f;
      assert s21.Peek(11) == 0x309;
      assert s21.Peek(16) == 0xee;
      var s22 := Dup6(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x59f;
      assert s31.Peek(11) == 0x309;
      assert s31.Peek(16) == 0xee;
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
      ExecuteFromCFGNode_s526(s41, gas - 1)
  }

  /** Node 526
    * Segment Id for this node is: 136
    * Starting at 0x9ce
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x59f

    requires s0.stack[8] == 0x309

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0x59f;
      assert s1.Peek(9) == 0x309;
      assert s1.Peek(14) == 0xee;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0a39);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s534(s4, gas - 1)
      else
        ExecuteFromCFGNode_s527(s4, gas - 1)
  }

  /** Node 527
    * Segment Id for this node is: 137
    * Starting at 0x9d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x59f

    requires s0.stack[8] == 0x309

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(5) == 0x59f;
      assert s1.Peek(9) == 0x309;
      assert s1.Peek(14) == 0xee;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup5(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x0a30);
      assert s11.Peek(0) == 0xa30;
      assert s11.Peek(10) == 0x59f;
      assert s11.Peek(14) == 0x309;
      assert s11.Peek(19) == 0xee;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0e13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s528(s15, gas - 1)
  }

  /** Node 528
    * Segment Id for this node is: 196
    * Starting at 0xe13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xa30

    requires s0.stack[10] == 0x59f

    requires s0.stack[14] == 0x309

    requires s0.stack[19] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa30;
      assert s1.Peek(10) == 0x59f;
      assert s1.Peek(14) == 0x309;
      assert s1.Peek(19) == 0xee;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0e26);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xe26;
      assert s11.Peek(5) == 0xa30;
      assert s11.Peek(13) == 0x59f;
      assert s11.Peek(17) == 0x309;
      assert s11.Peek(22) == 0xee;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0e04);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s529(s14, gas - 1)
  }

  /** Node 529
    * Segment Id for this node is: 194
    * Starting at 0xe04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xe26

    requires s0.stack[6] == 0xa30

    requires s0.stack[14] == 0x59f

    requires s0.stack[18] == 0x309

    requires s0.stack[23] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe26;
      assert s1.Peek(6) == 0xa30;
      assert s1.Peek(14) == 0x59f;
      assert s1.Peek(18) == 0x309;
      assert s1.Peek(23) == 0xee;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d60);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s530(s5, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 176
    * Starting at 0xd60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0xe26

    requires s0.stack[8] == 0xa30

    requires s0.stack[16] == 0x59f

    requires s0.stack[20] == 0x309

    requires s0.stack[25] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0xe26;
      assert s1.Peek(8) == 0xa30;
      assert s1.Peek(16) == 0x59f;
      assert s1.Peek(20) == 0x309;
      assert s1.Peek(25) == 0xee;
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
    * Segment Id for this node is: 195
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xe26

    requires s0.stack[7] == 0xa30

    requires s0.stack[15] == 0x59f

    requires s0.stack[19] == 0x309

    requires s0.stack[24] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe26;
      assert s1.Peek(7) == 0xa30;
      assert s1.Peek(15) == 0x59f;
      assert s1.Peek(19) == 0x309;
      assert s1.Peek(24) == 0xee;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s532(s6, gas - 1)
  }

  /** Node 532
    * Segment Id for this node is: 197
    * Starting at 0xe26
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xa30

    requires s0.stack[11] == 0x59f

    requires s0.stack[15] == 0x309

    requires s0.stack[20] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa30;
      assert s1.Peek(11) == 0x59f;
      assert s1.Peek(15) == 0x309;
      assert s1.Peek(20) == 0xee;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s533(s6, gas - 1)
  }

  /** Node 533
    * Segment Id for this node is: 138
    * Starting at 0xa30
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x59f

    requires s0.stack[12] == 0x309

    requires s0.stack[17] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x59f;
      assert s1.Peek(12) == 0x309;
      assert s1.Peek(17) == 0xee;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s534(s8, gas - 1)
  }

  /** Node 534
    * Segment Id for this node is: 139
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x59f

    requires s0.stack[8] == 0x309

    requires s0.stack[13] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x59f;
      assert s1.Peek(8) == 0x309;
      assert s1.Peek(13) == 0xee;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s535(s6, gas - 1)
  }

  /** Node 535
    * Segment Id for this node is: 103
    * Starting at 0x59f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x309

    requires s0.stack[8] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x309;
      assert s1.Peek(8) == 0xee;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s536(s5, gas - 1)
  }

  /** Node 536
    * Segment Id for this node is: 69
    * Starting at 0x309
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x309 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xee

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xee;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s537(s10, gas - 1)
  }

  /** Node 537
    * Segment Id for this node is: 23
    * Starting at 0xee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
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
      var s7 := Push2(s6, 0x0deb);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s538(s8, gas - 1)
  }

  /** Node 538
    * Segment Id for this node is: 192
    * Starting at 0xdeb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdeb as nat
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
      var s8 := Push2(s7, 0x0dfe);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xdfe;
      assert s11.Peek(5) == 0xfb;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0ddc);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s539(s14, gas - 1)
  }

  /** Node 539
    * Segment Id for this node is: 190
    * Starting at 0xddc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xddc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xdfe

    requires s0.stack[6] == 0xfb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdfe;
      assert s1.Peek(6) == 0xfb;
      var s2 := Push2(s1, 0x0de5);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0dd1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s540(s5, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 189
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xde5

    requires s0.stack[4] == 0xdfe

    requires s0.stack[8] == 0xfb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xde5;
      assert s1.Peek(4) == 0xdfe;
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
      ExecuteFromCFGNode_s541(s11, gas - 1)
  }

  /** Node 541
    * Segment Id for this node is: 191
    * Starting at 0xde5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xdfe

    requires s0.stack[7] == 0xfb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdfe;
      assert s1.Peek(7) == 0xfb;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s6, gas - 1)
  }

  /** Node 542
    * Segment Id for this node is: 193
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
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
      ExecuteFromCFGNode_s543(s6, gas - 1)
  }

  /** Node 543
    * Segment Id for this node is: 24
    * Starting at 0xfb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
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

  /** Node 544
    * Segment Id for this node is: 18
    * Starting at 0xb6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push2(s2, 0x0262);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s545(s4, gas - 1)
  }

  /** Node 545
    * Segment Id for this node is: 58
    * Starting at 0x262
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x262 as nat
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
      var s3 := Push1(s2, 0x03);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x0271);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0f6e);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s546(s9, gas - 1)
  }

  /** Node 546
    * Segment Id for this node is: 226
    * Starting at 0xf6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x271

    requires s0.stack[4] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x271;
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
      assert s11.Peek(4) == 0x271;
      assert s11.Peek(7) == 0xbe;
      var s12 := Push2(s11, 0x0f85);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s548(s13, gas - 1)
      else
        ExecuteFromCFGNode_s547(s13, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 227
    * Starting at 0xf7f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x271

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x271;
      assert s1.Peek(7) == 0xbe;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s548(s5, gas - 1)
  }

  /** Node 548
    * Segment Id for this node is: 228
    * Starting at 0xf85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x271

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x271;
      assert s1.Peek(6) == 0xbe;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0f98);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s551(s8, gas - 1)
      else
        ExecuteFromCFGNode_s549(s8, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 229
    * Starting at 0xf90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x271

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f97);
      assert s1.Peek(0) == 0xf97;
      assert s1.Peek(4) == 0x271;
      assert s1.Peek(7) == 0xbe;
      var s2 := Push2(s1, 0x0f41);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s550(s3, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 225
    * Starting at 0xf41
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xf97

    requires s0.stack[4] == 0x271

    requires s0.stack[7] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf97;
      assert s1.Peek(4) == 0x271;
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

  /** Node 551
    * Segment Id for this node is: 231
    * Starting at 0xf98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x271

    requires s0.stack[6] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x271;
      assert s1.Peek(6) == 0xbe;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s552(s6, gas - 1)
  }

  /** Node 552
    * Segment Id for this node is: 59
    * Starting at 0x271
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x271 as nat
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
      var s31 := Push2(s30, 0x029d);
      assert s31.Peek(0) == 0x29d;
      assert s31.Peek(8) == 0xbe;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0f6e);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s553(s34, gas - 1)
  }

  /** Node 553
    * Segment Id for this node is: 226
    * Starting at 0xf6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x29d

    requires s0.stack[8] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x29d;
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
      assert s11.Peek(4) == 0x29d;
      assert s11.Peek(11) == 0xbe;
      var s12 := Push2(s11, 0x0f85);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s555(s13, gas - 1)
      else
        ExecuteFromCFGNode_s554(s13, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 227
    * Starting at 0xf7f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x29d

    requires s0.stack[10] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x29d;
      assert s1.Peek(11) == 0xbe;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s555(s5, gas - 1)
  }

  /** Node 555
    * Segment Id for this node is: 228
    * Starting at 0xf85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x29d

    requires s0.stack[10] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x29d;
      assert s1.Peek(10) == 0xbe;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0f98);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s558(s8, gas - 1)
      else
        ExecuteFromCFGNode_s556(s8, gas - 1)
  }

  /** Node 556
    * Segment Id for this node is: 229
    * Starting at 0xf90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x29d

    requires s0.stack[10] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f97);
      assert s1.Peek(0) == 0xf97;
      assert s1.Peek(4) == 0x29d;
      assert s1.Peek(11) == 0xbe;
      var s2 := Push2(s1, 0x0f41);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s557(s3, gas - 1)
  }

  /** Node 557
    * Segment Id for this node is: 225
    * Starting at 0xf41
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s557(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xf97

    requires s0.stack[4] == 0x29d

    requires s0.stack[11] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf97;
      assert s1.Peek(4) == 0x29d;
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

  /** Node 558
    * Segment Id for this node is: 231
    * Starting at 0xf98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s558(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x29d

    requires s0.stack[10] == 0xbe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x29d;
      assert s1.Peek(10) == 0xbe;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s559(s6, gas - 1)
  }

  /** Node 559
    * Segment Id for this node is: 60
    * Starting at 0x29d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s559(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29d as nat
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
      var s4 := Push2(s3, 0x02e8);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s562(s5, gas - 1)
      else
        ExecuteFromCFGNode_s560(s5, gas - 1)
  }

  /** Node 560
    * Segment Id for this node is: 61
    * Starting at 0x2a4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s560(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a4 as nat
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
      var s4 := Push2(s3, 0x02bf);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s579(s5, gas - 1)
      else
        ExecuteFromCFGNode_s561(s5, gas - 1)
  }

  /** Node 561
    * Segment Id for this node is: 62
    * Starting at 0x2ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s561(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ac as nat
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
      var s13 := Push2(s12, 0x02e8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s562(s14, gas - 1)
  }

  /** Node 562
    * Segment Id for this node is: 66
    * Starting at 0x2e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s562(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e8 as nat
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
      ExecuteFromCFGNode_s563(s10, gas - 1)
  }

  /** Node 563
    * Segment Id for this node is: 19
    * Starting at 0xbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s563(s0: EState, gas: nat): (s': EState)
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
      var s7 := Push2(s6, 0x0ce2);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s564(s8, gas - 1)
  }

  /** Node 564
    * Segment Id for this node is: 164
    * Starting at 0xce2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s564(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce2 as nat
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
      var s15 := Push2(s14, 0x0cfa);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0caa);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s565(s19, gas - 1)
  }

  /** Node 565
    * Segment Id for this node is: 159
    * Starting at 0xcaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s565(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xcfa

    requires s0.stack[6] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcfa;
      assert s1.Peek(6) == 0xcb;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0cb4);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c58);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s566(s6, gas - 1)
  }

  /** Node 566
    * Segment Id for this node is: 152
    * Starting at 0xc58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s566(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xcb4

    requires s0.stack[5] == 0xcfa

    requires s0.stack[9] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcb4;
      assert s1.Peek(5) == 0xcfa;
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
      ExecuteFromCFGNode_s567(s10, gas - 1)
  }

  /** Node 567
    * Segment Id for this node is: 160
    * Starting at 0xcb4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s567(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xcfa

    requires s0.stack[8] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xcfa;
      assert s1.Peek(8) == 0xcb;
      var s2 := Push2(s1, 0x0cbe);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0c62);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s568(s6, gas - 1)
  }

  /** Node 568
    * Segment Id for this node is: 153
    * Starting at 0xc62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s568(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xcbe

    requires s0.stack[7] == 0xcfa

    requires s0.stack[11] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcbe;
      assert s1.Peek(7) == 0xcfa;
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
      assert s11.Peek(0) == 0xcbe;
      assert s11.Peek(8) == 0xcfa;
      assert s11.Peek(12) == 0xcb;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s569(s15, gas - 1)
  }

  /** Node 569
    * Segment Id for this node is: 161
    * Starting at 0xcbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s569(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xcfa

    requires s0.stack[9] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xcfa;
      assert s1.Peek(9) == 0xcb;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0cce);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0c72);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s570(s11, gas - 1)
  }

  /** Node 570
    * Segment Id for this node is: 154
    * Starting at 0xc72
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s570(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xcce

    requires s0.stack[8] == 0xcfa

    requires s0.stack[12] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcce;
      assert s1.Peek(8) == 0xcfa;
      assert s1.Peek(12) == 0xcb;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s571(s2, gas - 1)
  }

  /** Node 571
    * Segment Id for this node is: 155
    * Starting at 0xc74
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s571(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xcce

    requires s0.stack[9] == 0xcfa

    requires s0.stack[13] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xcce;
      assert s1.Peek(9) == 0xcfa;
      assert s1.Peek(13) == 0xcb;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c8f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s573(s7, gas - 1)
      else
        ExecuteFromCFGNode_s572(s7, gas - 1)
  }

  /** Node 572
    * Segment Id for this node is: 156
    * Starting at 0xc7d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s572(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xcce

    requires s0.stack[9] == 0xcfa

    requires s0.stack[13] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xcce;
      assert s1.Peek(10) == 0xcfa;
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
      assert s11.Peek(5) == 0xcce;
      assert s11.Peek(10) == 0xcfa;
      assert s11.Peek(14) == 0xcb;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0c74);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s571(s15, gas - 1)
  }

  /** Node 573
    * Segment Id for this node is: 157
    * Starting at 0xc8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s573(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xcce

    requires s0.stack[9] == 0xcfa

    requires s0.stack[13] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xcce;
      assert s1.Peek(9) == 0xcfa;
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
      ExecuteFromCFGNode_s574(s11, gas - 1)
  }

  /** Node 574
    * Segment Id for this node is: 162
    * Starting at 0xcce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s574(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xcfa

    requires s0.stack[8] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xcfa;
      assert s1.Peek(8) == 0xcb;
      var s2 := Push2(s1, 0x0cd7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c9a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s575(s5, gas - 1)
  }

  /** Node 575
    * Segment Id for this node is: 158
    * Starting at 0xc9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s575(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xcd7

    requires s0.stack[6] == 0xcfa

    requires s0.stack[10] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcd7;
      assert s1.Peek(6) == 0xcfa;
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
      assert s11.Peek(0) == 0xcd7;
      assert s11.Peek(7) == 0xcfa;
      assert s11.Peek(11) == 0xcb;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s576(s14, gas - 1)
  }

  /** Node 576
    * Segment Id for this node is: 163
    * Starting at 0xcd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s576(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xcfa

    requires s0.stack[9] == 0xcb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xcfa;
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
      ExecuteFromCFGNode_s577(s11, gas - 1)
  }

  /** Node 577
    * Segment Id for this node is: 165
    * Starting at 0xcfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s577(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
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
      ExecuteFromCFGNode_s578(s8, gas - 1)
  }

  /** Node 578
    * Segment Id for this node is: 20
    * Starting at 0xcb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s578(s0: EState, gas: nat): (s': EState)
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

  /** Node 579
    * Segment Id for this node is: 63
    * Starting at 0x2bf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s579(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
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
      ExecuteFromCFGNode_s580(s11, gas - 1)
  }

  /** Node 580
    * Segment Id for this node is: 64
    * Starting at 0x2cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s580(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cb as nat
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
      var s15 := Push2(s14, 0x02cb);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s580(s16, gas - 1)
      else
        ExecuteFromCFGNode_s581(s16, gas - 1)
  }

  /** Node 581
    * Segment Id for this node is: 65
    * Starting at 0x2df
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s581(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2df as nat
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
      ExecuteFromCFGNode_s562(s8, gas - 1)
  }

  /** Node 582
    * Segment Id for this node is: 17
    * Starting at 0xb2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s582(s0: EState, gas: nat): (s': EState)
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
