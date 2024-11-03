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
      var s6 := Push2(s5, 0x00c4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s243(s7, gas - 1)
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
      var s6 := Push4(s5, 0x313ce567);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x007d);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s9, gas - 1)
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
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0058);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s5, gas - 1)
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
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01d2);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01da);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s5, gas - 1)
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
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01ed);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s9(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x55
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
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
      var s1 := Push0(s0);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 9
    * Segment Id for this node is: 42
    * Starting at 0x1ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0122);
      var s3 := Push2(s2, 0x01fb);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0ac5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s7, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 132
    * Starting at 0xac5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1fb

    requires s0.stack[3] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(3) == 0x122;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0ad6);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s11, gas - 1)
      else
        ExecuteFromCFGNode_s11(s11, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 133
    * Starting at 0xad3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1fb

    requires s0.stack[5] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x1fb;
      assert s1.Peek(6) == 0x122;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 12
    * Segment Id for this node is: 134
    * Starting at 0xad6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1fb

    requires s0.stack[5] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1fb;
      assert s1.Peek(5) == 0x122;
      var s2 := Push2(s1, 0x0adf);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x08dc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s5, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 96
    * Starting at 0x8dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xadf

    requires s0.stack[6] == 0x1fb

    requires s0.stack[7] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xadf;
      assert s1.Peek(6) == 0x1fb;
      assert s1.Peek(7) == 0x122;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x08ff);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s10, gas - 1)
      else
        ExecuteFromCFGNode_s14(s10, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 97
    * Starting at 0x8fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xadf

    requires s0.stack[7] == 0x1fb

    requires s0.stack[8] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xadf;
      assert s1.Peek(8) == 0x1fb;
      assert s1.Peek(9) == 0x122;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 15
    * Segment Id for this node is: 98
    * Starting at 0x8ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xadf

    requires s0.stack[7] == 0x1fb

    requires s0.stack[8] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xadf;
      assert s1.Peek(7) == 0x1fb;
      assert s1.Peek(8) == 0x122;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s5, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 135
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1fb

    requires s0.stack[6] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1fb;
      assert s1.Peek(6) == 0x122;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0aed);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x08dc);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s9, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 96
    * Starting at 0x8dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xaed

    requires s0.stack[6] == 0x1fb

    requires s0.stack[7] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaed;
      assert s1.Peek(6) == 0x1fb;
      assert s1.Peek(7) == 0x122;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x08ff);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s10, gas - 1)
      else
        ExecuteFromCFGNode_s18(s10, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 97
    * Starting at 0x8fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xaed

    requires s0.stack[7] == 0x1fb

    requires s0.stack[8] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(8) == 0x1fb;
      assert s1.Peek(9) == 0x122;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 19
    * Segment Id for this node is: 98
    * Starting at 0x8ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xaed

    requires s0.stack[7] == 0x1fb

    requires s0.stack[8] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(7) == 0x1fb;
      assert s1.Peek(8) == 0x122;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s5, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 136
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1fb

    requires s0.stack[6] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1fb;
      assert s1.Peek(6) == 0x122;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s9, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 43
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x122;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Push0(s5);
      var s7 := Swap1(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(5) == 0x122;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup1(s15);
      var s17 := Dup4(s16);
      var s18 := Keccak256(s17);
      var s19 := Swap4(s18);
      var s20 := Swap1(s19);
      var s21 := Swap5(s20);
      assert s21.Peek(6) == 0x122;
      var s22 := And(s21);
      var s23 := Dup3(s22);
      var s24 := MStore(s23);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Swap2(s26);
      var s28 := MStore(s27);
      var s29 := Keccak256(s28);
      var s30 := SLoad(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(0) == 0x122;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s32, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 31
    * Starting at 0x122
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x00f2);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s10, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 26
    * Starting at 0xf2
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2 as nat
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

  /** Node 24
    * Segment Id for this node is: 40
    * Starting at 0x1da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x010e);
      var s3 := Push2(s2, 0x01e8);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0a4b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s7, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 120
    * Starting at 0xa4b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1e8

    requires s0.stack[3] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1e8;
      assert s1.Peek(3) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0a5c);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s11, gas - 1)
      else
        ExecuteFromCFGNode_s26(s11, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 121
    * Starting at 0xa59
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1e8

    requires s0.stack[5] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x1e8;
      assert s1.Peek(6) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 27
    * Segment Id for this node is: 122
    * Starting at 0xa5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1e8

    requires s0.stack[5] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1e8;
      assert s1.Peek(5) == 0x10e;
      var s2 := Push2(s1, 0x0a65);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x08dc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s5, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 96
    * Starting at 0x8dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xa65

    requires s0.stack[6] == 0x1e8

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa65;
      assert s1.Peek(6) == 0x1e8;
      assert s1.Peek(7) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x08ff);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s30(s10, gas - 1)
      else
        ExecuteFromCFGNode_s29(s10, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 97
    * Starting at 0x8fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xa65

    requires s0.stack[7] == 0x1e8

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xa65;
      assert s1.Peek(8) == 0x1e8;
      assert s1.Peek(9) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 30
    * Segment Id for this node is: 98
    * Starting at 0x8ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xa65

    requires s0.stack[7] == 0x1e8

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa65;
      assert s1.Peek(7) == 0x1e8;
      assert s1.Peek(8) == 0x10e;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s5, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 123
    * Starting at 0xa65
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1e8

    requires s0.stack[6] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1e8;
      assert s1.Peek(6) == 0x10e;
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
      assert s11.Peek(1) == 0x1e8;
      assert s11.Peek(4) == 0x10e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s13, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 41
    * Starting at 0x1e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10e;
      var s2 := Push2(s1, 0x04f4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s3, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 75
    * Starting at 0x4f4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0467);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x06bc);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s8, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 88
    * Starting at 0x6bc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x467

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x467;
      assert s1.Peek(7) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup4(s2);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x0745);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s6, gas - 1)
      else
        ExecuteFromCFGNode_s35(s6, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 89
    * Starting at 0x6d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x467

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x467;
      assert s1.Peek(8) == 0x10e;
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
      assert s11.Peek(6) == 0x467;
      assert s11.Peek(10) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x25);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x467;
      assert s21.Peek(10) == 0x10e;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6472657373000000000000000000000000000000000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0295);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s31, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 46
    * Starting at 0x295
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x467

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x467;
      assert s1.Peek(8) == 0x10e;
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

  /** Node 37
    * Segment Id for this node is: 90
    * Starting at 0x745
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x745 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x467

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x467;
      assert s1.Peek(7) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup3(s2);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x07ce);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s6, gas - 1)
      else
        ExecuteFromCFGNode_s38(s6, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 91
    * Starting at 0x761
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x761 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x467

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x467;
      assert s1.Peek(8) == 0x10e;
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
      assert s11.Peek(6) == 0x467;
      assert s11.Peek(10) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x23);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x467;
      assert s21.Peek(10) == 0x10e;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6573730000000000000000000000000000000000000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0295);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s31, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 92
    * Starting at 0x7ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x467

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x467;
      assert s1.Peek(7) == 0x10e;
      var s2 := Push2(s1, 0x0817);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(3) == 0x817;
      assert s11.Peek(7) == 0x467;
      assert s11.Peek(11) == 0x10e;
      var s12 := Push1(s11, 0x26);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0bec);
      var s18 := Push1(s17, 0x26);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push20(s20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s21.Peek(3) == 0x817;
      assert s21.Peek(7) == 0x467;
      assert s21.Peek(11) == 0x10e;
      var s22 := Dup7(s21);
      var s23 := And(s22);
      var s24 := Push0(s23);
      var s25 := Swap1(s24);
      var s26 := Dup2(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := MStore(s30);
      assert s31.Peek(3) == 0x817;
      assert s31.Peek(7) == 0x467;
      assert s31.Peek(11) == 0x10e;
      var s32 := Push1(s31, 0x40);
      var s33 := Swap1(s32);
      var s34 := Keccak256(s33);
      var s35 := SLoad(s34);
      var s36 := Swap2(s35);
      var s37 := Swap1(s36);
      var s38 := Push2(s37, 0x0500);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s39, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 76
    * Starting at 0x500
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x500 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x817

    requires s0.stack[7] == 0x467

    requires s0.stack[11] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x817;
      assert s1.Peek(7) == 0x467;
      assert s1.Peek(11) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0523);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s9, gas - 1)
      else
        ExecuteFromCFGNode_s41(s9, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 77
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x817

    requires s0.stack[9] == 0x467

    requires s0.stack[13] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x817;
      assert s1.Peek(10) == 0x467;
      assert s1.Peek(14) == 0x10e;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0295);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x295;
      assert s11.Peek(7) == 0x817;
      assert s11.Peek(11) == 0x467;
      assert s11.Peek(15) == 0x10e;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x09e2);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s14, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 116
    * Starting at 0x9e2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x295

    requires s0.stack[7] == 0x817

    requires s0.stack[11] == 0x467

    requires s0.stack[15] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x295;
      assert s1.Peek(7) == 0x817;
      assert s1.Peek(11) == 0x467;
      assert s1.Peek(15) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x295;
      assert s11.Peek(13) == 0x817;
      assert s11.Peek(17) == 0x467;
      assert s11.Peek(21) == 0x10e;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s43(s14, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 117
    * Starting at 0x9f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x817

    requires s0.stack[15] == 0x467

    requires s0.stack[19] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x295;
      assert s1.Peek(11) == 0x817;
      assert s1.Peek(15) == 0x467;
      assert s1.Peek(19) == 0x10e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a0d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s7, gas - 1)
      else
        ExecuteFromCFGNode_s44(s7, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 118
    * Starting at 0x9fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x817

    requires s0.stack[15] == 0x467

    requires s0.stack[19] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x295;
      assert s1.Peek(12) == 0x817;
      assert s1.Peek(16) == 0x467;
      assert s1.Peek(20) == 0x10e;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Add(s10);
      assert s11.Peek(8) == 0x295;
      assert s11.Peek(13) == 0x817;
      assert s11.Peek(17) == 0x467;
      assert s11.Peek(21) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x09f1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s16, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 119
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x817

    requires s0.stack[15] == 0x467

    requires s0.stack[19] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x295;
      assert s1.Peek(11) == 0x817;
      assert s1.Peek(15) == 0x467;
      assert s1.Peek(19) == 0x10e;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Push32(s10, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s11.Peek(7) == 0x295;
      assert s11.Peek(12) == 0x817;
      assert s11.Peek(16) == 0x467;
      assert s11.Peek(20) == 0x10e;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := And(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Add(s17);
      var s19 := Swap3(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0x295;
      assert s21.Peek(9) == 0x817;
      assert s21.Peek(13) == 0x467;
      assert s21.Peek(17) == 0x10e;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s27, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 46
    * Starting at 0x295
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x817

    requires s0.stack[9] == 0x467

    requires s0.stack[13] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x817;
      assert s1.Peek(9) == 0x467;
      assert s1.Peek(13) == 0x10e;
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

  /** Node 47
    * Segment Id for this node is: 78
    * Starting at 0x523
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x523 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x817

    requires s0.stack[9] == 0x467

    requires s0.stack[13] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x817;
      assert s1.Peek(9) == 0x467;
      assert s1.Peek(13) == 0x10e;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s8, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 93
    * Starting at 0x817
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x817 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x467

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x467;
      assert s1.Peek(8) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup1(s2);
      var s4 := Dup6(s3);
      var s5 := And(s4);
      var s6 := Push0(s5);
      var s7 := Swap1(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x467;
      assert s11.Peek(12) == 0x10e;
      var s12 := Swap1(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Keccak256(s16);
      var s18 := Swap4(s17);
      var s19 := Swap1(s18);
      var s20 := Swap4(s19);
      var s21 := SStore(s20);
      assert s21.Peek(6) == 0x467;
      assert s21.Peek(10) == 0x10e;
      var s22 := Swap1(s21);
      var s23 := Dup5(s22);
      var s24 := And(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Keccak256(s26);
      var s28 := SLoad(s27);
      var s29 := Push2(s28, 0x0852);
      var s30 := Swap1(s29);
      var s31 := Dup3(s30);
      assert s31.Peek(2) == 0x852;
      assert s31.Peek(6) == 0x467;
      assert s31.Peek(10) == 0x10e;
      var s32 := Push2(s31, 0x052b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s33, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 79
    * Starting at 0x52b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x852

    requires s0.stack[6] == 0x467

    requires s0.stack[10] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x852;
      assert s1.Peek(6) == 0x467;
      assert s1.Peek(10) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0536);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0bd8);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s7, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 147
    * Starting at 0xbd8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x536

    requires s0.stack[6] == 0x852

    requires s0.stack[10] == 0x467

    requires s0.stack[14] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x536;
      assert s1.Peek(6) == 0x852;
      assert s1.Peek(10) == 0x467;
      assert s1.Peek(14) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x046b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s10, gas - 1)
      else
        ExecuteFromCFGNode_s51(s10, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 148
    * Starting at 0xbe4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x536

    requires s0.stack[7] == 0x852

    requires s0.stack[11] == 0x467

    requires s0.stack[15] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x046b);
      assert s1.Peek(0) == 0x46b;
      assert s1.Peek(4) == 0x536;
      assert s1.Peek(8) == 0x852;
      assert s1.Peek(12) == 0x467;
      assert s1.Peek(16) == 0x10e;
      var s2 := Push2(s1, 0x0b23);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s3, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 138
    * Starting at 0xb23
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x46b

    requires s0.stack[4] == 0x536

    requires s0.stack[8] == 0x852

    requires s0.stack[12] == 0x467

    requires s0.stack[16] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x46b;
      assert s1.Peek(4) == 0x536;
      assert s1.Peek(8) == 0x852;
      assert s1.Peek(12) == 0x467;
      assert s1.Peek(16) == 0x10e;
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

  /** Node 53
    * Segment Id for this node is: 68
    * Starting at 0x46b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x536

    requires s0.stack[7] == 0x852

    requires s0.stack[11] == 0x467

    requires s0.stack[15] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x536;
      assert s1.Peek(7) == 0x852;
      assert s1.Peek(11) == 0x467;
      assert s1.Peek(15) == 0x10e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 80
    * Starting at 0x536
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x852

    requires s0.stack[8] == 0x467

    requires s0.stack[12] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x852;
      assert s1.Peek(8) == 0x467;
      assert s1.Peek(12) == 0x10e;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s7, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 94
    * Starting at 0x852
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x852 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x467

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x467;
      assert s1.Peek(8) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup4(s2);
      var s4 := Dup2(s3);
      var s5 := And(s4);
      var s6 := Push0(s5);
      var s7 := Dup2(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup2(s10);
      assert s11.Peek(9) == 0x467;
      assert s11.Peek(13) == 0x10e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Swap2(s14);
      var s16 := Dup3(s15);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := Swap5(s18);
      var s20 := Swap1(s19);
      var s21 := Swap5(s20);
      assert s21.Peek(9) == 0x467;
      assert s21.Peek(13) == 0x10e;
      var s22 := SStore(s21);
      var s23 := MLoad(s22);
      var s24 := Dup5(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Swap1(s26);
      var s28 := Swap3(s27);
      var s29 := Swap2(s28);
      var s30 := Dup7(s29);
      var s31 := And(s30);
      assert s31.Peek(7) == 0x467;
      assert s31.Peek(11) == 0x10e;
      var s32 := Swap2(s31);
      var s33 := Push32(s32, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s34 := Swap2(s33);
      var s35 := Add(s34);
      var s36 := Push2(s35, 0x06af);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s37, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 87
    * Starting at 0x6af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x467

    requires s0.stack[11] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x467;
      assert s1.Peek(11) == 0x10e;
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
      assert s11.Peek(0) == 0x467;
      assert s11.Peek(4) == 0x10e;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s12, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 67
    * Starting at 0x467
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x467 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10e;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s58(s3, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 68
    * Starting at 0x46b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s6, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 29
    * Starting at 0x10e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x00f2);
      assert s11.Peek(0) == 0xf2;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s12, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 39
    * Starting at 0x1d2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e5);
      var s3 := Push2(s2, 0x04e5);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s4, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 74
    * Starting at 0x4e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe5;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x03);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x03da);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0b87);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s9, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 142
    * Starting at 0xb87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x3da

    requires s0.stack[4] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3da;
      assert s1.Peek(4) == 0xe5;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x0b9b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s11, gas - 1)
      else
        ExecuteFromCFGNode_s63(s11, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 143
    * Starting at 0xb95
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb95 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3da

    requires s0.stack[6] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x3da;
      assert s1.Peek(7) == 0xe5;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s64(s5, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 144
    * Starting at 0xb9b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3da

    requires s0.stack[6] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3da;
      assert s1.Peek(6) == 0xe5;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0bd2);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s8, gas - 1)
      else
        ExecuteFromCFGNode_s65(s8, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 145
    * Starting at 0xba6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3da

    requires s0.stack[6] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push32(s0, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      assert s1.Peek(4) == 0x3da;
      assert s1.Peek(7) == 0xe5;
      var s2 := Push0(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x22);
      var s5 := Push1(s4, 0x04);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Push0(s7);
      var s9 := Revert(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 66
    * Segment Id for this node is: 146
    * Starting at 0xbd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3da

    requires s0.stack[6] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3da;
      assert s1.Peek(6) == 0xe5;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s6, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 58
    * Starting at 0x3da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe5;
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
      assert s11.Peek(4) == 0xe5;
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
      assert s21.Peek(5) == 0xe5;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x0406);
      assert s31.Peek(0) == 0x406;
      assert s31.Peek(8) == 0xe5;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0b87);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s34, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 142
    * Starting at 0xb87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x406

    requires s0.stack[8] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x406;
      assert s1.Peek(8) == 0xe5;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x0b9b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s11, gas - 1)
      else
        ExecuteFromCFGNode_s69(s11, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 143
    * Starting at 0xb95
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb95 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x406

    requires s0.stack[10] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x406;
      assert s1.Peek(11) == 0xe5;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s70(s5, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 144
    * Starting at 0xb9b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x406

    requires s0.stack[10] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x406;
      assert s1.Peek(10) == 0xe5;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0bd2);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s8, gas - 1)
      else
        ExecuteFromCFGNode_s71(s8, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 145
    * Starting at 0xba6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x406

    requires s0.stack[10] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push32(s0, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      assert s1.Peek(4) == 0x406;
      assert s1.Peek(11) == 0xe5;
      var s2 := Push0(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x22);
      var s5 := Push1(s4, 0x04);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Push0(s7);
      var s9 := Revert(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 72
    * Segment Id for this node is: 146
    * Starting at 0xbd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x406

    requires s0.stack[10] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x406;
      assert s1.Peek(10) == 0xe5;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s6, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 59
    * Starting at 0x406
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x406 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xe5;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0451);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s5, gas - 1)
      else
        ExecuteFromCFGNode_s74(s5, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 60
    * Starting at 0x40d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0xe5;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0428);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s82(s5, gas - 1)
      else
        ExecuteFromCFGNode_s75(s5, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 61
    * Starting at 0x415
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x415 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0xe5;
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
      assert s11.Peek(7) == 0xe5;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0451);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s14, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 65
    * Starting at 0x451
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x451 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xe5;
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
      ExecuteFromCFGNode_s77(s10, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 25
    * Starting at 0xe5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00f2);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x09e2);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s8, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 116
    * Starting at 0x9e2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xf2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf2;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0xf2;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s79(s14, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 117
    * Starting at 0x9f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xf2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xf2;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a0d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s7, gas - 1)
      else
        ExecuteFromCFGNode_s80(s7, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 118
    * Starting at 0x9fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xf2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0xf2;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Add(s10);
      assert s11.Peek(8) == 0xf2;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x09f1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s16, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 119
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xf2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xf2;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Push32(s10, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s11.Peek(7) == 0xf2;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := And(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Add(s17);
      var s19 := Swap3(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xf2;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s27, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 62
    * Starting at 0x428
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x428 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xe5;
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
      ExecuteFromCFGNode_s83(s11, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 63
    * Starting at 0x434
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x434 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xe5;
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
      assert s11.Peek(7) == 0xe5;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x0434);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s16, gas - 1)
      else
        ExecuteFromCFGNode_s84(s16, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 64
    * Starting at 0x448
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x448 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0xe5;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s76(s8, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 9
    * Starting at 0x58
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x313ce567);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0143);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s6, gas - 1)
      else
        ExecuteFromCFGNode_s86(s6, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 10
    * Starting at 0x64
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x64744e33);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0158);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s5, gas - 1)
      else
        ExecuteFromCFGNode_s87(s5, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 11
    * Starting at 0x6f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x019d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s5, gas - 1)
      else
        ExecuteFromCFGNode_s88(s5, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 12
    * Starting at 0x7a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a as nat
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

  /** Node 89
    * Segment Id for this node is: 37
    * Starting at 0x19d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0122);
      var s3 := Push2(s2, 0x01ab);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0aac);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s7, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 129
    * Starting at 0xaac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1ab

    requires s0.stack[3] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ab;
      assert s1.Peek(3) == 0x122;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0abc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s10, gas - 1)
      else
        ExecuteFromCFGNode_s91(s10, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 130
    * Starting at 0xab9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1ab

    requires s0.stack[4] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x1ab;
      assert s1.Peek(5) == 0x122;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 92
    * Segment Id for this node is: 131
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1ab

    requires s0.stack[4] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1ab;
      assert s1.Peek(4) == 0x122;
      var s2 := Push2(s1, 0x0536);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x08dc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s5, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 96
    * Starting at 0x8dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x536

    requires s0.stack[5] == 0x1ab

    requires s0.stack[6] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x536;
      assert s1.Peek(5) == 0x1ab;
      assert s1.Peek(6) == 0x122;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x08ff);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s10, gas - 1)
      else
        ExecuteFromCFGNode_s94(s10, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 97
    * Starting at 0x8fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x536

    requires s0.stack[6] == 0x1ab

    requires s0.stack[7] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x536;
      assert s1.Peek(7) == 0x1ab;
      assert s1.Peek(8) == 0x122;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 95
    * Segment Id for this node is: 98
    * Starting at 0x8ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x536

    requires s0.stack[6] == 0x1ab

    requires s0.stack[7] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x536;
      assert s1.Peek(6) == 0x1ab;
      assert s1.Peek(7) == 0x122;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s5, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 80
    * Starting at 0x536
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1ab

    requires s0.stack[5] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1ab;
      assert s1.Peek(5) == 0x122;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s7, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 38
    * Starting at 0x1ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x122

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x122;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup2(s8);
      var s10 := Swap1(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x122;
      var s12 := Push1(s11, 0x40);
      var s13 := Swap1(s12);
      var s14 := Keccak256(s13);
      var s15 := SLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s17, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 35
    * Starting at 0x158
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x158 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0178);
      var s5 := Swap1(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s9, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 36
    * Starting at 0x178
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x178 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x178

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x178;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Swap1(s4);
      var s6 := Swap2(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x178;
      var s12 := Push2(s11, 0x00f2);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s13, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 26
    * Starting at 0xf2
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x178

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x178;
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

  /** Node 101
    * Segment Id for this node is: 34
    * Starting at 0x143
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x04);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0xff);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Push2(s13, 0x00f2);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s15, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 13
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x095ea7b3);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00ad);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s181(s6, gas - 1)
      else
        ExecuteFromCFGNode_s103(s6, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 14
    * Starting at 0x89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00fb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s5, gas - 1)
      else
        ExecuteFromCFGNode_s104(s5, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 15
    * Starting at 0x94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x011e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s5, gas - 1)
      else
        ExecuteFromCFGNode_s105(s5, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 16
    * Starting at 0x9f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0130);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s5, gas - 1)
      else
        ExecuteFromCFGNode_s106(s5, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 17
    * Starting at 0xaa
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa as nat
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

  /** Node 107
    * Segment Id for this node is: 32
    * Starting at 0x130
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x130 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x010e);
      var s3 := Push2(s2, 0x013e);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0a73);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s7, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 124
    * Starting at 0xa73
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x13e

    requires s0.stack[3] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13e;
      assert s1.Peek(3) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0a85);
      assert s11.Peek(0) == 0xa85;
      assert s11.Peek(7) == 0x13e;
      assert s11.Peek(8) == 0x10e;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s12, gas - 1)
      else
        ExecuteFromCFGNode_s109(s12, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 125
    * Starting at 0xa82
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x13e

    requires s0.stack[6] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 110
    * Segment Id for this node is: 126
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x13e

    requires s0.stack[6] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x13e;
      assert s1.Peek(6) == 0x10e;
      var s2 := Push2(s1, 0x0a8e);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x08dc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s5, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 96
    * Starting at 0x8dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xa8e

    requires s0.stack[7] == 0x13e

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa8e;
      assert s1.Peek(7) == 0x13e;
      assert s1.Peek(8) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x08ff);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s113(s10, gas - 1)
      else
        ExecuteFromCFGNode_s112(s10, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 97
    * Starting at 0x8fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xa8e

    requires s0.stack[8] == 0x13e

    requires s0.stack[9] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xa8e;
      assert s1.Peek(9) == 0x13e;
      assert s1.Peek(10) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 113
    * Segment Id for this node is: 98
    * Starting at 0x8ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xa8e

    requires s0.stack[8] == 0x13e

    requires s0.stack[9] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa8e;
      assert s1.Peek(8) == 0x13e;
      assert s1.Peek(9) == 0x10e;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s5, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 127
    * Starting at 0xa8e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x13e

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x10e;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a9c);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x08dc);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s9, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 96
    * Starting at 0x8dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xa9c

    requires s0.stack[7] == 0x13e

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa9c;
      assert s1.Peek(7) == 0x13e;
      assert s1.Peek(8) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x08ff);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s117(s10, gas - 1)
      else
        ExecuteFromCFGNode_s116(s10, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 97
    * Starting at 0x8fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xa9c

    requires s0.stack[8] == 0x13e

    requires s0.stack[9] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xa9c;
      assert s1.Peek(9) == 0x13e;
      assert s1.Peek(10) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 117
    * Segment Id for this node is: 98
    * Starting at 0x8ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xa9c

    requires s0.stack[8] == 0x13e

    requires s0.stack[9] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa9c;
      assert s1.Peek(8) == 0x13e;
      assert s1.Peek(9) == 0x10e;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s5, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 128
    * Starting at 0xa9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x13e

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x13e;
      assert s1.Peek(7) == 0x10e;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Swap3(s9);
      var s11 := Pop(s10);
      assert s11.Peek(4) == 0x13e;
      assert s11.Peek(5) == 0x10e;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Swap3(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s15, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 33
    * Starting at 0x13e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10e;
      var s2 := Push2(s1, 0x0471);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s3, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 69
    * Starting at 0x471
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x471 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x047d);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x06bc);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s8, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 88
    * Starting at 0x6bc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47d

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x47d;
      assert s1.Peek(8) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup4(s2);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x0745);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s124(s6, gas - 1)
      else
        ExecuteFromCFGNode_s122(s6, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 89
    * Starting at 0x6d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47d

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x47d;
      assert s1.Peek(9) == 0x10e;
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
      assert s11.Peek(6) == 0x47d;
      assert s11.Peek(11) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x25);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x47d;
      assert s21.Peek(11) == 0x10e;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6472657373000000000000000000000000000000000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0295);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s31, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 46
    * Starting at 0x295
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x47d

    requires s0.stack[9] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x47d;
      assert s1.Peek(9) == 0x10e;
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

  /** Node 124
    * Segment Id for this node is: 90
    * Starting at 0x745
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x745 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47d

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x47d;
      assert s1.Peek(8) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup3(s2);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x07ce);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s126(s6, gas - 1)
      else
        ExecuteFromCFGNode_s125(s6, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 91
    * Starting at 0x761
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x761 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47d

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x47d;
      assert s1.Peek(9) == 0x10e;
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
      assert s11.Peek(6) == 0x47d;
      assert s11.Peek(11) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x23);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x47d;
      assert s21.Peek(11) == 0x10e;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6573730000000000000000000000000000000000000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0295);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s31, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 92
    * Starting at 0x7ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x47d

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x47d;
      assert s1.Peek(8) == 0x10e;
      var s2 := Push2(s1, 0x0817);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(3) == 0x817;
      assert s11.Peek(7) == 0x47d;
      assert s11.Peek(12) == 0x10e;
      var s12 := Push1(s11, 0x26);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0bec);
      var s18 := Push1(s17, 0x26);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push20(s20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s21.Peek(3) == 0x817;
      assert s21.Peek(7) == 0x47d;
      assert s21.Peek(12) == 0x10e;
      var s22 := Dup7(s21);
      var s23 := And(s22);
      var s24 := Push0(s23);
      var s25 := Swap1(s24);
      var s26 := Dup2(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := MStore(s30);
      assert s31.Peek(3) == 0x817;
      assert s31.Peek(7) == 0x47d;
      assert s31.Peek(12) == 0x10e;
      var s32 := Push1(s31, 0x40);
      var s33 := Swap1(s32);
      var s34 := Keccak256(s33);
      var s35 := SLoad(s34);
      var s36 := Swap2(s35);
      var s37 := Swap1(s36);
      var s38 := Push2(s37, 0x0500);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s39, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 76
    * Starting at 0x500
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x500 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x817

    requires s0.stack[7] == 0x47d

    requires s0.stack[12] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x817;
      assert s1.Peek(7) == 0x47d;
      assert s1.Peek(12) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0523);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s134(s9, gas - 1)
      else
        ExecuteFromCFGNode_s128(s9, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 77
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x817

    requires s0.stack[9] == 0x47d

    requires s0.stack[14] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x817;
      assert s1.Peek(10) == 0x47d;
      assert s1.Peek(15) == 0x10e;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0295);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x295;
      assert s11.Peek(7) == 0x817;
      assert s11.Peek(11) == 0x47d;
      assert s11.Peek(16) == 0x10e;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x09e2);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s14, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 116
    * Starting at 0x9e2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x295

    requires s0.stack[7] == 0x817

    requires s0.stack[11] == 0x47d

    requires s0.stack[16] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x295;
      assert s1.Peek(7) == 0x817;
      assert s1.Peek(11) == 0x47d;
      assert s1.Peek(16) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x295;
      assert s11.Peek(13) == 0x817;
      assert s11.Peek(17) == 0x47d;
      assert s11.Peek(22) == 0x10e;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s130(s14, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 117
    * Starting at 0x9f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x817

    requires s0.stack[15] == 0x47d

    requires s0.stack[20] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x295;
      assert s1.Peek(11) == 0x817;
      assert s1.Peek(15) == 0x47d;
      assert s1.Peek(20) == 0x10e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a0d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s7, gas - 1)
      else
        ExecuteFromCFGNode_s131(s7, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 118
    * Starting at 0x9fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x817

    requires s0.stack[15] == 0x47d

    requires s0.stack[20] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x295;
      assert s1.Peek(12) == 0x817;
      assert s1.Peek(16) == 0x47d;
      assert s1.Peek(21) == 0x10e;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Add(s10);
      assert s11.Peek(8) == 0x295;
      assert s11.Peek(13) == 0x817;
      assert s11.Peek(17) == 0x47d;
      assert s11.Peek(22) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x09f1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s16, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 119
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x817

    requires s0.stack[15] == 0x47d

    requires s0.stack[20] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x295;
      assert s1.Peek(11) == 0x817;
      assert s1.Peek(15) == 0x47d;
      assert s1.Peek(20) == 0x10e;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Push32(s10, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s11.Peek(7) == 0x295;
      assert s11.Peek(12) == 0x817;
      assert s11.Peek(16) == 0x47d;
      assert s11.Peek(21) == 0x10e;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := And(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Add(s17);
      var s19 := Swap3(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0x295;
      assert s21.Peek(9) == 0x817;
      assert s21.Peek(13) == 0x47d;
      assert s21.Peek(18) == 0x10e;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s27, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 46
    * Starting at 0x295
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x817

    requires s0.stack[9] == 0x47d

    requires s0.stack[14] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x817;
      assert s1.Peek(9) == 0x47d;
      assert s1.Peek(14) == 0x10e;
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

  /** Node 134
    * Segment Id for this node is: 78
    * Starting at 0x523
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x523 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x817

    requires s0.stack[9] == 0x47d

    requires s0.stack[14] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x817;
      assert s1.Peek(9) == 0x47d;
      assert s1.Peek(14) == 0x10e;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s8, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 93
    * Starting at 0x817
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x817 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x47d

    requires s0.stack[9] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x47d;
      assert s1.Peek(9) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup1(s2);
      var s4 := Dup6(s3);
      var s5 := And(s4);
      var s6 := Push0(s5);
      var s7 := Swap1(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x47d;
      assert s11.Peek(13) == 0x10e;
      var s12 := Swap1(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Keccak256(s16);
      var s18 := Swap4(s17);
      var s19 := Swap1(s18);
      var s20 := Swap4(s19);
      var s21 := SStore(s20);
      assert s21.Peek(6) == 0x47d;
      assert s21.Peek(11) == 0x10e;
      var s22 := Swap1(s21);
      var s23 := Dup5(s22);
      var s24 := And(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Keccak256(s26);
      var s28 := SLoad(s27);
      var s29 := Push2(s28, 0x0852);
      var s30 := Swap1(s29);
      var s31 := Dup3(s30);
      assert s31.Peek(2) == 0x852;
      assert s31.Peek(6) == 0x47d;
      assert s31.Peek(11) == 0x10e;
      var s32 := Push2(s31, 0x052b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s33, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 79
    * Starting at 0x52b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x852

    requires s0.stack[6] == 0x47d

    requires s0.stack[11] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x852;
      assert s1.Peek(6) == 0x47d;
      assert s1.Peek(11) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0536);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0bd8);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s7, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 147
    * Starting at 0xbd8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x536

    requires s0.stack[6] == 0x852

    requires s0.stack[10] == 0x47d

    requires s0.stack[15] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x536;
      assert s1.Peek(6) == 0x852;
      assert s1.Peek(10) == 0x47d;
      assert s1.Peek(15) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x046b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s140(s10, gas - 1)
      else
        ExecuteFromCFGNode_s138(s10, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 148
    * Starting at 0xbe4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x536

    requires s0.stack[7] == 0x852

    requires s0.stack[11] == 0x47d

    requires s0.stack[16] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x046b);
      assert s1.Peek(0) == 0x46b;
      assert s1.Peek(4) == 0x536;
      assert s1.Peek(8) == 0x852;
      assert s1.Peek(12) == 0x47d;
      assert s1.Peek(17) == 0x10e;
      var s2 := Push2(s1, 0x0b23);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s3, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 138
    * Starting at 0xb23
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0x46b

    requires s0.stack[4] == 0x536

    requires s0.stack[8] == 0x852

    requires s0.stack[12] == 0x47d

    requires s0.stack[17] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x46b;
      assert s1.Peek(4) == 0x536;
      assert s1.Peek(8) == 0x852;
      assert s1.Peek(12) == 0x47d;
      assert s1.Peek(17) == 0x10e;
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

  /** Node 140
    * Segment Id for this node is: 68
    * Starting at 0x46b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x536

    requires s0.stack[7] == 0x852

    requires s0.stack[11] == 0x47d

    requires s0.stack[16] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x536;
      assert s1.Peek(7) == 0x852;
      assert s1.Peek(11) == 0x47d;
      assert s1.Peek(16) == 0x10e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s6, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 80
    * Starting at 0x536
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x852

    requires s0.stack[8] == 0x47d

    requires s0.stack[13] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x852;
      assert s1.Peek(8) == 0x47d;
      assert s1.Peek(13) == 0x10e;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s7, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 94
    * Starting at 0x852
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x852 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x47d

    requires s0.stack[9] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x47d;
      assert s1.Peek(9) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup4(s2);
      var s4 := Dup2(s3);
      var s5 := And(s4);
      var s6 := Push0(s5);
      var s7 := Dup2(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup2(s10);
      assert s11.Peek(9) == 0x47d;
      assert s11.Peek(14) == 0x10e;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Swap2(s14);
      var s16 := Dup3(s15);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := Swap5(s18);
      var s20 := Swap1(s19);
      var s21 := Swap5(s20);
      assert s21.Peek(9) == 0x47d;
      assert s21.Peek(14) == 0x10e;
      var s22 := SStore(s21);
      var s23 := MLoad(s22);
      var s24 := Dup5(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Swap1(s26);
      var s28 := Swap3(s27);
      var s29 := Swap2(s28);
      var s30 := Dup7(s29);
      var s31 := And(s30);
      assert s31.Peek(7) == 0x47d;
      assert s31.Peek(12) == 0x10e;
      var s32 := Swap2(s31);
      var s33 := Push32(s32, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s34 := Swap2(s33);
      var s35 := Add(s34);
      var s36 := Push2(s35, 0x06af);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s37, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 87
    * Starting at 0x6af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x47d

    requires s0.stack[12] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x47d;
      assert s1.Peek(12) == 0x10e;
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
      assert s11.Peek(0) == 0x47d;
      assert s11.Peek(5) == 0x10e;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s12, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 70
    * Starting at 0x47d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +12
    * Net Capacity Effect: -12
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10e;
      var s2 := Push2(s1, 0x04db);
      var s3 := Dup5(s2);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x04d6);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x60);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x4d6;
      assert s11.Peek(6) == 0x4db;
      assert s11.Peek(11) == 0x10e;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := Push1(s14, 0x28);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Add(s18);
      var s20 := Push2(s19, 0x0c12);
      var s21 := Push1(s20, 0x28);
      assert s21.Peek(5) == 0x4d6;
      assert s21.Peek(8) == 0x4db;
      assert s21.Peek(13) == 0x10e;
      var s22 := Swap2(s21);
      var s23 := CodeCopy(s22);
      var s24 := Push20(s23, 0xffffffffffffffffffffffffffffffffffffffff);
      var s25 := Dup11(s24);
      var s26 := And(s25);
      var s27 := Push0(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x01);
      assert s31.Peek(4) == 0x4d6;
      assert s31.Peek(7) == 0x4db;
      assert s31.Peek(12) == 0x10e;
      var s32 := Push1(s31, 0x20);
      var s33 := Swap1(s32);
      var s34 := Dup2(s33);
      var s35 := MStore(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := Dup1(s36);
      var s38 := Dup4(s37);
      var s39 := Keccak256(s38);
      var s40 := Caller(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s145(s41, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 71
    * Starting at 0x4c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x4d6

    requires s0.stack[11] == 0x4db

    requires s0.stack[16] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.Peek(6) == 0x4d6;
      assert s1.Peek(9) == 0x4db;
      assert s1.Peek(14) == 0x10e;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := MStore(s3);
      var s5 := Swap1(s4);
      var s6 := Keccak256(s5);
      var s7 := SLoad(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0500);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s11, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 76
    * Starting at 0x500
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x500 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x4d6

    requires s0.stack[6] == 0x4db

    requires s0.stack[11] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4d6;
      assert s1.Peek(6) == 0x4db;
      assert s1.Peek(11) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0523);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s153(s9, gas - 1)
      else
        ExecuteFromCFGNode_s147(s9, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 77
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x4d6

    requires s0.stack[8] == 0x4db

    requires s0.stack[13] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x4d6;
      assert s1.Peek(9) == 0x4db;
      assert s1.Peek(14) == 0x10e;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0295);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x295;
      assert s11.Peek(7) == 0x4d6;
      assert s11.Peek(10) == 0x4db;
      assert s11.Peek(15) == 0x10e;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x09e2);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s14, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 116
    * Starting at 0x9e2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x295

    requires s0.stack[7] == 0x4d6

    requires s0.stack[10] == 0x4db

    requires s0.stack[15] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x295;
      assert s1.Peek(7) == 0x4d6;
      assert s1.Peek(10) == 0x4db;
      assert s1.Peek(15) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x295;
      assert s11.Peek(13) == 0x4d6;
      assert s11.Peek(16) == 0x4db;
      assert s11.Peek(21) == 0x10e;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s149(s14, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 117
    * Starting at 0x9f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x4d6

    requires s0.stack[14] == 0x4db

    requires s0.stack[19] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x295;
      assert s1.Peek(11) == 0x4d6;
      assert s1.Peek(14) == 0x4db;
      assert s1.Peek(19) == 0x10e;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a0d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s7, gas - 1)
      else
        ExecuteFromCFGNode_s150(s7, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 118
    * Starting at 0x9fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x4d6

    requires s0.stack[14] == 0x4db

    requires s0.stack[19] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x295;
      assert s1.Peek(12) == 0x4d6;
      assert s1.Peek(15) == 0x4db;
      assert s1.Peek(20) == 0x10e;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Add(s10);
      assert s11.Peek(8) == 0x295;
      assert s11.Peek(13) == 0x4d6;
      assert s11.Peek(16) == 0x4db;
      assert s11.Peek(21) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x09f1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s16, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 119
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x4d6

    requires s0.stack[14] == 0x4db

    requires s0.stack[19] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x295;
      assert s1.Peek(11) == 0x4d6;
      assert s1.Peek(14) == 0x4db;
      assert s1.Peek(19) == 0x10e;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Push32(s10, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s11.Peek(7) == 0x295;
      assert s11.Peek(12) == 0x4d6;
      assert s11.Peek(15) == 0x4db;
      assert s11.Peek(20) == 0x10e;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := And(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Add(s17);
      var s19 := Swap3(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0x295;
      assert s21.Peek(9) == 0x4d6;
      assert s21.Peek(12) == 0x4db;
      assert s21.Peek(17) == 0x10e;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s27, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 46
    * Starting at 0x295
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x4d6

    requires s0.stack[8] == 0x4db

    requires s0.stack[13] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4d6;
      assert s1.Peek(8) == 0x4db;
      assert s1.Peek(13) == 0x10e;
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

  /** Node 153
    * Segment Id for this node is: 78
    * Starting at 0x523
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x523 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x4d6

    requires s0.stack[8] == 0x4db

    requires s0.stack[13] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4d6;
      assert s1.Peek(8) == 0x4db;
      assert s1.Peek(13) == 0x10e;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s8, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 72
    * Starting at 0x4d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x4db

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4db;
      assert s1.Peek(8) == 0x10e;
      var s2 := Push2(s1, 0x053d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s3, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 81
    * Starting at 0x53d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x4db

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4db;
      assert s1.Peek(8) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup4(s2);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x05c5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s158(s6, gas - 1)
      else
        ExecuteFromCFGNode_s156(s6, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 82
    * Starting at 0x559
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x559 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x4db

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x4db;
      assert s1.Peek(9) == 0x10e;
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
      assert s11.Peek(6) == 0x4db;
      assert s11.Peek(11) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup1(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x4db;
      assert s21.Peek(11) == 0x10e;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0295);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s31, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 46
    * Starting at 0x295
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x4db

    requires s0.stack[9] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4db;
      assert s1.Peek(9) == 0x10e;
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

  /** Node 158
    * Segment Id for this node is: 83
    * Starting at 0x5c5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x4db

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4db;
      assert s1.Peek(8) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup3(s2);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x064e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s160(s6, gas - 1)
      else
        ExecuteFromCFGNode_s159(s6, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 84
    * Starting at 0x5e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x4db

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x4db;
      assert s1.Peek(9) == 0x10e;
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
      assert s11.Peek(6) == 0x4db;
      assert s11.Peek(11) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x22);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x4db;
      assert s21.Peek(11) == 0x10e;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0295);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s31, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 85
    * Starting at 0x64e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x4db

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4db;
      assert s1.Peek(8) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup4(s2);
      var s4 := Dup2(s3);
      var s5 := And(s4);
      var s6 := Push0(s5);
      var s7 := Dup2(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(8) == 0x4db;
      assert s11.Peek(13) == 0x10e;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup1(s15);
      var s17 := Dup4(s16);
      var s18 := Keccak256(s17);
      var s19 := Swap5(s18);
      var s20 := Dup8(s19);
      var s21 := And(s20);
      assert s21.Peek(9) == 0x4db;
      assert s21.Peek(14) == 0x10e;
      var s22 := Dup1(s21);
      var s23 := Dup5(s22);
      var s24 := MStore(s23);
      var s25 := Swap5(s24);
      var s26 := Dup3(s25);
      var s27 := MStore(s26);
      var s28 := Swap2(s27);
      var s29 := Dup3(s28);
      var s30 := Swap1(s29);
      var s31 := Keccak256(s30);
      assert s31.Peek(8) == 0x4db;
      assert s31.Peek(13) == 0x10e;
      var s32 := Dup6(s31);
      var s33 := Swap1(s32);
      var s34 := SStore(s33);
      var s35 := Swap1(s34);
      var s36 := MLoad(s35);
      var s37 := Dup5(s36);
      var s38 := Dup2(s37);
      var s39 := MStore(s38);
      var s40 := Push32(s39, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s161(s41, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 86
    * Starting at 0x6ae
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x4db

    requires s0.stack[13] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s162(s1, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 87
    * Starting at 0x6af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x4db

    requires s0.stack[12] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x4db;
      assert s1.Peek(12) == 0x10e;
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
      assert s11.Peek(0) == 0x4db;
      assert s11.Peek(5) == 0x10e;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s12, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 73
    * Starting at 0x4db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10e;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap4(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s9, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 30
    * Starting at 0x11e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s22(s3, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 27
    * Starting at 0xfb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x010e);
      var s3 := Push2(s2, 0x0109);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0a4b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s7, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 120
    * Starting at 0xa4b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x109

    requires s0.stack[3] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x109;
      assert s1.Peek(3) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0a5c);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s168(s11, gas - 1)
      else
        ExecuteFromCFGNode_s167(s11, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 121
    * Starting at 0xa59
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x109

    requires s0.stack[5] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x109;
      assert s1.Peek(6) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 168
    * Segment Id for this node is: 122
    * Starting at 0xa5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x109

    requires s0.stack[5] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x109;
      assert s1.Peek(5) == 0x10e;
      var s2 := Push2(s1, 0x0a65);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x08dc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s5, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 96
    * Starting at 0x8dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xa65

    requires s0.stack[6] == 0x109

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa65;
      assert s1.Peek(6) == 0x109;
      assert s1.Peek(7) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x08ff);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s171(s10, gas - 1)
      else
        ExecuteFromCFGNode_s170(s10, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 97
    * Starting at 0x8fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xa65

    requires s0.stack[7] == 0x109

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xa65;
      assert s1.Peek(8) == 0x109;
      assert s1.Peek(9) == 0x10e;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 171
    * Segment Id for this node is: 98
    * Starting at 0x8ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xa65

    requires s0.stack[7] == 0x109

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa65;
      assert s1.Peek(7) == 0x109;
      assert s1.Peek(8) == 0x10e;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s5, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 123
    * Starting at 0xa65
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x109

    requires s0.stack[6] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x109;
      assert s1.Peek(6) == 0x10e;
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
      assert s11.Peek(1) == 0x109;
      assert s11.Peek(4) == 0x10e;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s13, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 28
    * Starting at 0x109
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10e;
      var s2 := Push2(s1, 0x045b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s3, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 66
    * Starting at 0x45b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0467);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x053d);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s8, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 81
    * Starting at 0x53d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x467

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x467;
      assert s1.Peek(7) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup4(s2);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x05c5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s6, gas - 1)
      else
        ExecuteFromCFGNode_s176(s6, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 82
    * Starting at 0x559
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x559 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x467

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x467;
      assert s1.Peek(8) == 0x10e;
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
      assert s11.Peek(6) == 0x467;
      assert s11.Peek(10) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup1(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x467;
      assert s21.Peek(10) == 0x10e;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0295);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s31, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 83
    * Starting at 0x5c5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x467

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x467;
      assert s1.Peek(7) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup3(s2);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x064e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s179(s6, gas - 1)
      else
        ExecuteFromCFGNode_s178(s6, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 84
    * Starting at 0x5e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x467

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x467;
      assert s1.Peek(8) == 0x10e;
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
      assert s11.Peek(6) == 0x467;
      assert s11.Peek(10) == 0x10e;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x22);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x467;
      assert s21.Peek(10) == 0x10e;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0295);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s31, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 85
    * Starting at 0x64e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x467

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x467;
      assert s1.Peek(7) == 0x10e;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup4(s2);
      var s4 := Dup2(s3);
      var s5 := And(s4);
      var s6 := Push0(s5);
      var s7 := Dup2(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(8) == 0x467;
      assert s11.Peek(12) == 0x10e;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup1(s15);
      var s17 := Dup4(s16);
      var s18 := Keccak256(s17);
      var s19 := Swap5(s18);
      var s20 := Dup8(s19);
      var s21 := And(s20);
      assert s21.Peek(9) == 0x467;
      assert s21.Peek(13) == 0x10e;
      var s22 := Dup1(s21);
      var s23 := Dup5(s22);
      var s24 := MStore(s23);
      var s25 := Swap5(s24);
      var s26 := Dup3(s25);
      var s27 := MStore(s26);
      var s28 := Swap2(s27);
      var s29 := Dup3(s28);
      var s30 := Swap1(s29);
      var s31 := Keccak256(s30);
      assert s31.Peek(8) == 0x467;
      assert s31.Peek(12) == 0x10e;
      var s32 := Dup6(s31);
      var s33 := Swap1(s32);
      var s34 := SStore(s33);
      var s35 := Swap1(s34);
      var s36 := MLoad(s35);
      var s37 := Dup5(s36);
      var s38 := Dup2(s37);
      var s39 := MStore(s38);
      var s40 := Push32(s39, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s180(s41, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 86
    * Starting at 0x6ae
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x467

    requires s0.stack[12] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s56(s1, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 18
    * Starting at 0xad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x05081983);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00c8);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s6, gas - 1)
      else
        ExecuteFromCFGNode_s182(s6, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 19
    * Starting at 0xb9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x06fdde03);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00dd);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s184(s5, gas - 1)
      else
        ExecuteFromCFGNode_s183(s5, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 20
    * Starting at 0xc4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4 as nat
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

  /** Node 184
    * Segment Id for this node is: 24
    * Starting at 0xdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e5);
      var s3 := Push2(s2, 0x03cb);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s4, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 57
    * Starting at 0x3cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xe5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe5;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x03da);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0b87);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s9, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 21
    * Starting at 0xc8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00db);
      var s3 := Push2(s2, 0x00d6);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0904);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s7, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 99
    * Starting at 0x904
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x904 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xd6

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd6;
      assert s1.Peek(3) == 0xdb;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0915);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s11, gas - 1)
      else
        ExecuteFromCFGNode_s188(s11, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 100
    * Starting at 0x912
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x912 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xd6

    requires s0.stack[5] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0xd6;
      assert s1.Peek(6) == 0xdb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 189
    * Segment Id for this node is: 101
    * Starting at 0x915
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x915 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xd6

    requires s0.stack[5] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd6;
      assert s1.Peek(5) == 0xdb;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x092c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s10, gas - 1)
      else
        ExecuteFromCFGNode_s190(s10, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 102
    * Starting at 0x929
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x929 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xd6

    requires s0.stack[7] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0xd6;
      assert s1.Peek(8) == 0xdb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 191
    * Segment Id for this node is: 103
    * Starting at 0x92c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xd6

    requires s0.stack[7] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xd6;
      assert s1.Peek(7) == 0xdb;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup6(s6);
      var s8 := Push1(s7, 0x1f);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := SLt(s10);
      assert s11.Peek(7) == 0xd6;
      assert s11.Peek(8) == 0xdb;
      var s12 := Push2(s11, 0x093f);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s13, gas - 1)
      else
        ExecuteFromCFGNode_s192(s13, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 104
    * Starting at 0x93c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xd6

    requires s0.stack[7] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0xd6;
      assert s1.Peek(8) == 0xdb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 193
    * Segment Id for this node is: 105
    * Starting at 0x93f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xd6

    requires s0.stack[7] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xd6;
      assert s1.Peek(7) == 0xdb;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0951);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s196(s9, gas - 1)
      else
        ExecuteFromCFGNode_s194(s9, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 106
    * Starting at 0x94a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0xd6

    requires s0.stack[8] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0951);
      assert s1.Peek(0) == 0x951;
      assert s1.Peek(8) == 0xd6;
      assert s1.Peek(9) == 0xdb;
      var s2 := Push2(s1, 0x08af);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s3, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 95
    * Starting at 0x8af
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x951

    requires s0.stack[8] == 0xd6

    requires s0.stack[9] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x951;
      assert s1.Peek(8) == 0xd6;
      assert s1.Peek(9) == 0xdb;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 196
    * Segment Id for this node is: 107
    * Starting at 0x951
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x951 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0xd6

    requires s0.stack[8] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xd6;
      assert s1.Peek(8) == 0xdb;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Push1(s7, 0x3f);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := And(s10);
      assert s11.Peek(10) == 0xd6;
      assert s11.Peek(11) == 0xdb;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Dup2(s13);
      var s15 := Dup2(s14);
      var s16 := Lt(s15);
      var s17 := Dup6(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Or(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(11) == 0xd6;
      assert s21.Peek(12) == 0xdb;
      var s22 := Push2(s21, 0x0994);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s23, gas - 1)
      else
        ExecuteFromCFGNode_s197(s23, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 108
    * Starting at 0x98d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0xd6

    requires s0.stack[11] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0994);
      assert s1.Peek(0) == 0x994;
      assert s1.Peek(11) == 0xd6;
      assert s1.Peek(12) == 0xdb;
      var s2 := Push2(s1, 0x08af);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s3, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 95
    * Starting at 0x8af
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x994

    requires s0.stack[11] == 0xd6

    requires s0.stack[12] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x994;
      assert s1.Peek(11) == 0xd6;
      assert s1.Peek(12) == 0xdb;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 199
    * Segment Id for this node is: 109
    * Starting at 0x994
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x994 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0xd6

    requires s0.stack[11] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xd6;
      assert s1.Peek(11) == 0xdb;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Dup3(s4);
      var s6 := MStore(s5);
      var s7 := Dup5(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Swap3(s9);
      var s11 := Pop(s10);
      assert s11.Peek(8) == 0xd6;
      assert s11.Peek(9) == 0xdb;
      var s12 := Dup4(s11);
      var s13 := Dup2(s12);
      var s14 := Add(s13);
      var s15 := Dup6(s14);
      var s16 := Add(s15);
      var s17 := Swap2(s16);
      var s18 := Dup9(s17);
      var s19 := Dup4(s18);
      var s20 := Gt(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(10) == 0xd6;
      assert s21.Peek(11) == 0xdb;
      var s22 := Push2(s21, 0x09b1);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s23, gas - 1)
      else
        ExecuteFromCFGNode_s200(s23, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 110
    * Starting at 0x9ae
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0xd6

    requires s0.stack[10] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(10) == 0xd6;
      assert s1.Peek(11) == 0xdb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 201
    * Segment Id for this node is: 111
    * Starting at 0x9b1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0xd6

    requires s0.stack[10] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xd6;
      assert s1.Peek(10) == 0xdb;
      var s2 := Swap4(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Swap4(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s202(s5, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 112
    * Starting at 0x9b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0xd6

    requires s0.stack[10] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xd6;
      assert s1.Peek(10) == 0xdb;
      var s2 := Dup3(s1);
      var s3 := Dup6(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x09d6);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s208(s7, gas - 1)
      else
        ExecuteFromCFGNode_s203(s7, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 113
    * Starting at 0x9bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0xd6

    requires s0.stack[10] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09c7);
      assert s1.Peek(0) == 0x9c7;
      assert s1.Peek(10) == 0xd6;
      assert s1.Peek(11) == 0xdb;
      var s2 := Dup6(s1);
      var s3 := Push2(s2, 0x08dc);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s4, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 96
    * Starting at 0x8dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x9c7

    requires s0.stack[11] == 0xd6

    requires s0.stack[12] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9c7;
      assert s1.Peek(11) == 0xd6;
      assert s1.Peek(12) == 0xdb;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x08ff);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s10, gas - 1)
      else
        ExecuteFromCFGNode_s205(s10, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 97
    * Starting at 0x8fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x9c7

    requires s0.stack[12] == 0xd6

    requires s0.stack[13] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x9c7;
      assert s1.Peek(13) == 0xd6;
      assert s1.Peek(14) == 0xdb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 206
    * Segment Id for this node is: 98
    * Starting at 0x8ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x9c7

    requires s0.stack[12] == 0xd6

    requires s0.stack[13] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9c7;
      assert s1.Peek(12) == 0xd6;
      assert s1.Peek(13) == 0xdb;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s5, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 114
    * Starting at 0x9c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0xd6

    requires s0.stack[11] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xd6;
      assert s1.Peek(11) == 0xdb;
      var s2 := Dup5(s1);
      var s3 := MStore(s2);
      var s4 := Swap4(s3);
      var s5 := Dup6(s4);
      var s6 := Add(s5);
      var s7 := Swap4(s6);
      var s8 := Swap3(s7);
      var s9 := Dup6(s8);
      var s10 := Add(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(9) == 0xd6;
      assert s11.Peek(10) == 0xdb;
      var s12 := Push2(s11, 0x09b6);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s13, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 115
    * Starting at 0x9d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0xd6

    requires s0.stack[10] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xd6;
      assert s1.Peek(10) == 0xdb;
      var s2 := Swap(s1, 9);
      var s3 := Swap(s2, 8);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0xd6;
      assert s11.Peek(2) == 0xdb;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s12, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 22
    * Starting at 0xd6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdb;
      var s2 := Push2(s1, 0x0232);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s3, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 44
    * Starting at 0x232
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x232 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdb;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Caller(s5);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x029e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s213(s9, gas - 1)
      else
        ExecuteFromCFGNode_s211(s9, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 45
    * Starting at 0x252
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x252 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0xdb;
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
      assert s11.Peek(4) == 0xdb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4e6f7420616c6c6f776564000000000000000000000000000000000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0xdb;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s212(s24, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 46
    * Starting at 0x295
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb;
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

  /** Node 213
    * Segment Id for this node is: 47
    * Starting at 0x29e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdb;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s214(s2, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 48
    * Starting at 0x2a0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x03c7);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s241(s8, gas - 1)
      else
        ExecuteFromCFGNode_s215(s8, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 49
    * Starting at 0x2aa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xdb;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Dup2(s3);
      var s5 := MLoad(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := Push2(s7, 0x02bc);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s9, gas - 1)
      else
        ExecuteFromCFGNode_s216(s9, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 50
    * Starting at 0x2b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02bc);
      assert s1.Peek(0) == 0x2bc;
      assert s1.Peek(6) == 0xdb;
      var s2 := Push2(s1, 0x0af6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s3, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 137
    * Starting at 0xaf6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x2bc

    requires s0.stack[6] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2bc;
      assert s1.Peek(6) == 0xdb;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 218
    * Segment Id for this node is: 51
    * Starting at 0x2bc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xdb;
      var s2 := Push1(s1, 0x20);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := Mul(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0xdb;
      var s12 := MLoad(s11);
      var s13 := Push20(s12, 0xffffffffffffffffffffffffffffffffffffffff);
      var s14 := Dup2(s13);
      var s15 := And(s14);
      var s16 := Push0(s15);
      var s17 := Dup2(s16);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := Dup5(s20);
      assert s21.Peek(9) == 0xdb;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x40);
      var s24 := Dup1(s23);
      var s25 := Dup3(s24);
      var s26 := Keccak256(s25);
      var s27 := SLoad(s26);
      var s28 := Dup2(s27);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(12) == 0xdb;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Swap3(s33);
      var s35 := MStore(s34);
      var s36 := Push1(s35, 0x05);
      var s37 := Dup3(s36);
      var s38 := MStore(s37);
      var s39 := Push32(s38, 0x4552524f52000000000000000000000000000000000000000000000000000000);
      var s40 := Dup3(s39);
      var s41 := Dup8(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s219(s41, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 52
    * Starting at 0x31c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      assert s1.Peek(11) == 0xdb;
      var s2 := MStore(s1);
      var s3 := Swap3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Swap4(s5);
      var s7 := MStore(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := Pop(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(5) == 0xdb;
      var s12 := Push2(s11, 0x0333);
      var s13 := Swap1(s12);
      var s14 := Dup3(s13);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x0500);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s19, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 76
    * Starting at 0x500
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x500 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x333

    requires s0.stack[8] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x333;
      assert s1.Peek(8) == 0xdb;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0523);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s227(s9, gas - 1)
      else
        ExecuteFromCFGNode_s221(s9, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 77
    * Starting at 0x50b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x333

    requires s0.stack[10] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x333;
      assert s1.Peek(11) == 0xdb;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0295);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x295;
      assert s11.Peek(7) == 0x333;
      assert s11.Peek(12) == 0xdb;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x09e2);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s14, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 116
    * Starting at 0x9e2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x295

    requires s0.stack[7] == 0x333

    requires s0.stack[12] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x295;
      assert s1.Peek(7) == 0x333;
      assert s1.Peek(12) == 0xdb;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x295;
      assert s11.Peek(13) == 0x333;
      assert s11.Peek(18) == 0xdb;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s223(s14, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 117
    * Starting at 0x9f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x333

    requires s0.stack[16] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x295;
      assert s1.Peek(11) == 0x333;
      assert s1.Peek(16) == 0xdb;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a0d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s225(s7, gas - 1)
      else
        ExecuteFromCFGNode_s224(s7, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 118
    * Starting at 0x9fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x333

    requires s0.stack[16] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x295;
      assert s1.Peek(12) == 0x333;
      assert s1.Peek(17) == 0xdb;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Add(s10);
      assert s11.Peek(8) == 0x295;
      assert s11.Peek(13) == 0x333;
      assert s11.Peek(18) == 0xdb;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x09f1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s16, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 119
    * Starting at 0xa0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x295

    requires s0.stack[11] == 0x333

    requires s0.stack[16] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x295;
      assert s1.Peek(11) == 0x333;
      assert s1.Peek(16) == 0xdb;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Push32(s10, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s11.Peek(7) == 0x295;
      assert s11.Peek(12) == 0x333;
      assert s11.Peek(17) == 0xdb;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := And(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Add(s17);
      var s19 := Swap3(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0x295;
      assert s21.Peek(9) == 0x333;
      assert s21.Peek(14) == 0xdb;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s27, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 46
    * Starting at 0x295
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x333

    requires s0.stack[10] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x333;
      assert s1.Peek(10) == 0xdb;
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

  /** Node 227
    * Segment Id for this node is: 78
    * Starting at 0x523
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x523 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x333

    requires s0.stack[10] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x333;
      assert s1.Peek(10) == 0xdb;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s8, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 53
    * Starting at 0x333
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x333 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xdb;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup4(s2);
      var s4 := And(s3);
      var s5 := Push0(s4);
      var s6 := Swap1(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0xdb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup2(s13);
      var s15 := Keccak256(s14);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := SStore(s18);
      var s20 := Dup1(s19);
      var s21 := MStore(s20);
      assert s21.Peek(4) == 0xdb;
      var s22 := Push32(s21, 0xad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5);
      var s23 := SLoad(s22);
      var s24 := Push2(s23, 0x0389);
      var s25 := Swap1(s24);
      var s26 := Dup3(s25);
      var s27 := Push2(s26, 0x052b);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s28, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 79
    * Starting at 0x52b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x389

    requires s0.stack[7] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x389;
      assert s1.Peek(7) == 0xdb;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0536);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0bd8);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s230(s7, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 147
    * Starting at 0xbd8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x536

    requires s0.stack[6] == 0x389

    requires s0.stack[11] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x536;
      assert s1.Peek(6) == 0x389;
      assert s1.Peek(11) == 0xdb;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x046b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s233(s10, gas - 1)
      else
        ExecuteFromCFGNode_s231(s10, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 148
    * Starting at 0xbe4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x536

    requires s0.stack[7] == 0x389

    requires s0.stack[12] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x046b);
      assert s1.Peek(0) == 0x46b;
      assert s1.Peek(4) == 0x536;
      assert s1.Peek(8) == 0x389;
      assert s1.Peek(13) == 0xdb;
      var s2 := Push2(s1, 0x0b23);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s3, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 138
    * Starting at 0xb23
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x46b

    requires s0.stack[4] == 0x536

    requires s0.stack[8] == 0x389

    requires s0.stack[13] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x46b;
      assert s1.Peek(4) == 0x536;
      assert s1.Peek(8) == 0x389;
      assert s1.Peek(13) == 0xdb;
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

  /** Node 233
    * Segment Id for this node is: 68
    * Starting at 0x46b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x536

    requires s0.stack[7] == 0x389

    requires s0.stack[12] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x536;
      assert s1.Peek(7) == 0x389;
      assert s1.Peek(12) == 0xdb;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s6, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 80
    * Starting at 0x536
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x536 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x389

    requires s0.stack[9] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x389;
      assert s1.Peek(9) == 0xdb;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s7, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 54
    * Starting at 0x389
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x389 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xdb;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup1(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := MStore(s6);
      var s8 := Push32(s7, 0xad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5);
      var s9 := SStore(s8);
      var s10 := Pop(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0xdb;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x03bf);
      var s15 := Dup2(s14);
      var s16 := Push2(s15, 0x0b50);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s17, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 139
    * Starting at 0xb50
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x3bf

    requires s0.stack[5] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3bf;
      assert s1.Peek(5) == 0xdb;
      var s2 := Push0(s1);
      var s3 := Push32(s2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0b80);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s239(s7, gas - 1)
      else
        ExecuteFromCFGNode_s237(s7, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 140
    * Starting at 0xb79
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x3bf

    requires s0.stack[6] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b80);
      assert s1.Peek(0) == 0xb80;
      assert s1.Peek(3) == 0x3bf;
      assert s1.Peek(7) == 0xdb;
      var s2 := Push2(s1, 0x0b23);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s3, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 138
    * Starting at 0xb23
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xb80

    requires s0.stack[3] == 0x3bf

    requires s0.stack[7] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb80;
      assert s1.Peek(3) == 0x3bf;
      assert s1.Peek(7) == 0xdb;
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

  /** Node 239
    * Segment Id for this node is: 141
    * Starting at 0xb80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x3bf

    requires s0.stack[6] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3bf;
      assert s1.Peek(6) == 0xdb;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s240(s6, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 55
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xdb;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push2(s4, 0x02a0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s6, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 56
    * Starting at 0x3c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s4, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 23
    * Starting at 0xdb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb as nat
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

  /** Node 243
    * Segment Id for this node is: 20
    * Starting at 0xc4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4 as nat
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
