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
      var s6 := Push2(s5, 0x00f0);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s264(s7, gas - 1)
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
      var s6 := Push4(s5, 0x70a08231);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x0093);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s9, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0063);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s80(s5, gas - 1)
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
      var s4 := Push2(s3, 0x01dc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s30(s5, gas - 1)
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
      var s2 := Push4(s1, 0xbb8a4c94);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01ef);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s5, gas - 1)
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
      var s4 := Push2(s3, 0x021a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s13(s5, gas - 1)
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
      var s2 := Push4(s1, 0xf851a440);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0252);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x60
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
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
      var s1 := Push0(s0);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 10
    * Segment Id for this node is: 52
    * Starting at 0x252
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x252 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Push2(s9, 0x0202);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s11, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 49
    * Starting at 0x202
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x202 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Swap1(s8);
      var s10 := Swap2(s9);
      var s11 := And(s10);
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0113);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s17, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 28
    * Starting at 0x113
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113 as nat
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

  /** Node 13
    * Segment Id for this node is: 50
    * Starting at 0x21a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x016a);
      var s3 := Push2(s2, 0x0228);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x09b9);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s7, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 133
    * Starting at 0x9b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x228

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x228;
      assert s1.Peek(3) == 0x16a;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x09ca);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s11, gas - 1)
      else
        ExecuteFromCFGNode_s15(s11, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 134
    * Starting at 0x9c7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x228

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x228;
      assert s1.Peek(6) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 16
    * Segment Id for this node is: 135
    * Starting at 0x9ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x228

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x228;
      assert s1.Peek(5) == 0x16a;
      var s2 := Push2(s1, 0x09d3);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x08d1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s5, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 113
    * Starting at 0x8d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x9d3

    requires s0.stack[6] == 0x228

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9d3;
      assert s1.Peek(6) == 0x228;
      assert s1.Peek(7) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x9d3;
      assert s11.Peek(9) == 0x228;
      assert s11.Peek(10) == 0x16a;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x08e7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s14, gas - 1)
      else
        ExecuteFromCFGNode_s18(s14, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 114
    * Starting at 0x8e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x9d3

    requires s0.stack[7] == 0x228

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x9d3;
      assert s1.Peek(8) == 0x228;
      assert s1.Peek(9) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 19
    * Segment Id for this node is: 115
    * Starting at 0x8e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x9d3

    requires s0.stack[7] == 0x228

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9d3;
      assert s1.Peek(7) == 0x228;
      assert s1.Peek(8) == 0x16a;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s5, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 136
    * Starting at 0x9d3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x228

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x228;
      assert s1.Peek(6) == 0x16a;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x09e1);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x08d1);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s9, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 113
    * Starting at 0x8d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x9e1

    requires s0.stack[6] == 0x228

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9e1;
      assert s1.Peek(6) == 0x228;
      assert s1.Peek(7) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x9e1;
      assert s11.Peek(9) == 0x228;
      assert s11.Peek(10) == 0x16a;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x08e7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s14, gas - 1)
      else
        ExecuteFromCFGNode_s22(s14, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 114
    * Starting at 0x8e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x9e1

    requires s0.stack[7] == 0x228

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x9e1;
      assert s1.Peek(8) == 0x228;
      assert s1.Peek(9) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 23
    * Segment Id for this node is: 115
    * Starting at 0x8e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x9e1

    requires s0.stack[7] == 0x228

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9e1;
      assert s1.Peek(7) == 0x228;
      assert s1.Peek(8) == 0x16a;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s5, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 137
    * Starting at 0x9e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x228

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x228;
      assert s1.Peek(6) == 0x16a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s9, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 51
    * Starting at 0x228
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x228 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap2(s6);
      var s8 := Dup3(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x16a;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x06);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(7) == 0x16a;
      var s22 := Keccak256(s21);
      var s23 := Swap4(s22);
      var s24 := Swap1(s23);
      var s25 := Swap5(s24);
      var s26 := And(s25);
      var s27 := Dup3(s26);
      var s28 := MStore(s27);
      var s29 := Swap2(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(4) == 0x16a;
      var s32 := MStore(s31);
      var s33 := Keccak256(s32);
      var s34 := SLoad(s33);
      var s35 := Swap1(s34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s36, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 36
    * Starting at 0x16a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16a as nat
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
      var s9 := Push2(s8, 0x0113);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s10, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 48
    * Starting at 0x1ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x04);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0202);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(1) == 0x202;
      var s12 := Dup2(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s13, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 49
    * Starting at 0x202
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x202 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x202

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x202;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Swap1(s8);
      var s10 := Swap2(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x202;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0113);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s17, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 28
    * Starting at 0x113
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x202

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x202;
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

  /** Node 30
    * Segment Id for this node is: 46
    * Starting at 0x1dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0107);
      var s3 := Push2(s2, 0x01ea);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0958);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s7, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 124
    * Starting at 0x958
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x958 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1ea

    requires s0.stack[3] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ea;
      assert s1.Peek(3) == 0x107;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0969);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s11, gas - 1)
      else
        ExecuteFromCFGNode_s32(s11, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 125
    * Starting at 0x966
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x966 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1ea

    requires s0.stack[5] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x1ea;
      assert s1.Peek(6) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 33
    * Segment Id for this node is: 126
    * Starting at 0x969
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x969 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1ea

    requires s0.stack[5] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1ea;
      assert s1.Peek(5) == 0x107;
      var s2 := Push2(s1, 0x0972);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x08d1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s5, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 113
    * Starting at 0x8d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x972

    requires s0.stack[6] == 0x1ea

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x972;
      assert s1.Peek(6) == 0x1ea;
      assert s1.Peek(7) == 0x107;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x972;
      assert s11.Peek(9) == 0x1ea;
      assert s11.Peek(10) == 0x107;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x08e7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s14, gas - 1)
      else
        ExecuteFromCFGNode_s35(s14, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 114
    * Starting at 0x8e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x972

    requires s0.stack[7] == 0x1ea

    requires s0.stack[8] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x972;
      assert s1.Peek(8) == 0x1ea;
      assert s1.Peek(9) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 36
    * Segment Id for this node is: 115
    * Starting at 0x8e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x972

    requires s0.stack[7] == 0x1ea

    requires s0.stack[8] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x972;
      assert s1.Peek(7) == 0x1ea;
      assert s1.Peek(8) == 0x107;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s5, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 127
    * Starting at 0x972
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x972 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1ea

    requires s0.stack[6] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1ea;
      assert s1.Peek(6) == 0x107;
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
      assert s11.Peek(1) == 0x1ea;
      assert s11.Peek(4) == 0x107;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s13, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 47
    * Starting at 0x1ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x107;
      var s2 := Push2(s1, 0x03f0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s3, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 80
    * Starting at 0x3f0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x107;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02aa);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x05bb);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s8, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 94
    * Starting at 0x5bb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2aa;
      assert s1.Peek(7) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x061f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s10, gas - 1)
      else
        ExecuteFromCFGNode_s41(s10, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 95
    * Starting at 0x5ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2aa;
      assert s1.Peek(8) == 0x107;
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
      assert s11.Peek(6) == 0x2aa;
      assert s11.Peek(10) == 0x107;
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
      assert s21.Peek(6) == 0x2aa;
      assert s21.Peek(10) == 0x107;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 5, 0x6472657373);
      var s24 := Push1(s23, 0xd8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x2aa;
      assert s31.Peek(8) == 0x107;
      var s32 := Push2(s31, 0x045a);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s33, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 83
    * Starting at 0x45a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2aa

    requires s0.stack[8] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2aa;
      assert s1.Peek(8) == 0x107;
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

  /** Node 43
    * Segment Id for this node is: 96
    * Starting at 0x61f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2aa;
      assert s1.Peek(7) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0681);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s10, gas - 1)
      else
        ExecuteFromCFGNode_s44(s10, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 97
    * Starting at 0x62e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2aa;
      assert s1.Peek(8) == 0x107;
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
      assert s11.Peek(6) == 0x2aa;
      assert s11.Peek(10) == 0x107;
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
      assert s21.Peek(6) == 0x2aa;
      assert s21.Peek(10) == 0x107;
      var s22 := MStore(s21);
      var s23 := Push3(s22, 0x657373);
      var s24 := Push1(s23, 0xe8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x2aa;
      assert s31.Peek(8) == 0x107;
      var s32 := Push2(s31, 0x045a);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s33, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 98
    * Starting at 0x681
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x681 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2aa;
      assert s1.Peek(7) == 0x107;
      var s2 := Push1(s1, 0x0a);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := And(s9);
      var s11 := Push0(s10);
      assert s11.Peek(6) == 0x2aa;
      assert s11.Peek(10) == 0x107;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x07);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap1(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x2aa;
      assert s21.Peek(9) == 0x107;
      var s22 := Push1(s21, 0xff);
      var s23 := Swap2(s22);
      var s24 := Dup3(s23);
      var s25 := And(s24);
      var s26 := IsZero(s25);
      var s27 := IsZero(s26);
      var s28 := Swap2(s27);
      var s29 := And(s28);
      var s30 := IsZero(s29);
      var s31 := IsZero(s30);
      assert s31.Peek(5) == 0x2aa;
      assert s31.Peek(9) == 0x107;
      var s32 := Sub(s31);
      var s33 := Push2(s32, 0x06ff);
      var s34 := JumpI(s33);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s33.stack[1] > 0 then
        ExecuteFromCFGNode_s62(s34, gas - 1)
      else
        ExecuteFromCFGNode_s46(s34, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 99
    * Starting at 0x6ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x08);
      assert s1.Peek(4) == 0x2aa;
      assert s1.Peek(8) == 0x107;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup5(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0x2aa;
      assert s11.Peek(10) == 0x107;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x05);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Keccak256(s18);
      var s20 := SLoad(s19);
      var s21 := PushN(s20, 16, 0xffffffffffffffffffffffffffffffff);
      assert s21.Peek(6) == 0x2aa;
      assert s21.Peek(10) == 0x107;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := And(s23);
      var s25 := Swap1(s24);
      var s26 := Dup2(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x06e8);
      var s29 := Swap1(s28);
      var s30 := Dup3(s29);
      var s31 := Push2(s30, 0x0a36);
      assert s31.Peek(0) == 0xa36;
      assert s31.Peek(3) == 0x6e8;
      assert s31.Peek(9) == 0x2aa;
      assert s31.Peek(13) == 0x107;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s32, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 144
    * Starting at 0xa36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x6e8

    requires s0.stack[8] == 0x2aa

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6e8;
      assert s1.Peek(8) == 0x2aa;
      assert s1.Peek(12) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s10, gas - 1)
      else
        ExecuteFromCFGNode_s48(s10, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 145
    * Starting at 0xa42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x6e8

    requires s0.stack[9] == 0x2aa

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6e8;
      assert s1.Peek(10) == 0x2aa;
      assert s1.Peek(14) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s3, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x6e8

    requires s0.stack[10] == 0x2aa

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6e8;
      assert s1.Peek(10) == 0x2aa;
      assert s1.Peek(14) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x6e8;
      assert s11.Peek(12) == 0x2aa;
      assert s11.Peek(16) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 50
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x6e8

    requires s0.stack[9] == 0x2aa

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6e8;
      assert s1.Peek(9) == 0x2aa;
      assert s1.Peek(13) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s6, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 100
    * Starting at 0x6e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x2aa

    requires s0.stack[10] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2aa;
      assert s1.Peek(10) == 0x107;
      var s2 := Push2(s1, 0x06f2);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0a36);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s6, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 144
    * Starting at 0xa36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x6f2

    requires s0.stack[7] == 0x2aa

    requires s0.stack[11] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6f2;
      assert s1.Peek(7) == 0x2aa;
      assert s1.Peek(11) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s10, gas - 1)
      else
        ExecuteFromCFGNode_s53(s10, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 145
    * Starting at 0xa42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x6f2

    requires s0.stack[8] == 0x2aa

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6f2;
      assert s1.Peek(9) == 0x2aa;
      assert s1.Peek(13) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s3, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x6f2

    requires s0.stack[9] == 0x2aa

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6f2;
      assert s1.Peek(9) == 0x2aa;
      assert s1.Peek(13) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x6f2;
      assert s11.Peek(11) == 0x2aa;
      assert s11.Peek(15) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 55
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x6f2

    requires s0.stack[8] == 0x2aa

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6f2;
      assert s1.Peek(8) == 0x2aa;
      assert s1.Peek(12) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s6, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 101
    * Starting at 0x6f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x2aa

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2aa;
      assert s1.Peek(9) == 0x107;
      var s2 := Push2(s1, 0x06fc);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0a49);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s6, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 146
    * Starting at 0xa49
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x6fc

    requires s0.stack[6] == 0x2aa

    requires s0.stack[10] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6fc;
      assert s1.Peek(6) == 0x2aa;
      assert s1.Peek(10) == 0x107;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s10, gas - 1)
      else
        ExecuteFromCFGNode_s58(s10, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 147
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x6fc

    requires s0.stack[7] == 0x2aa

    requires s0.stack[11] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6fc;
      assert s1.Peek(8) == 0x2aa;
      assert s1.Peek(12) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s3, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x6fc

    requires s0.stack[8] == 0x2aa

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6fc;
      assert s1.Peek(8) == 0x2aa;
      assert s1.Peek(12) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x6fc;
      assert s11.Peek(10) == 0x2aa;
      assert s11.Peek(14) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 60
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x6fc

    requires s0.stack[7] == 0x2aa

    requires s0.stack[11] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6fc;
      assert s1.Peek(7) == 0x2aa;
      assert s1.Peek(11) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s6, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 102
    * Starting at 0x6fc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2aa

    requires s0.stack[8] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2aa;
      assert s1.Peek(8) == 0x107;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s62(s3, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 103
    * Starting at 0x6ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2aa;
      assert s1.Peek(7) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push0(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x2aa;
      assert s11.Peek(10) == 0x107;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x05);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Dup2(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x2aa;
      assert s21.Peek(10) == 0x107;
      var s22 := Lt(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x0776);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s25, gas - 1)
      else
        ExecuteFromCFGNode_s63(s25, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 104
    * Starting at 0x720
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x720 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2aa

    requires s0.stack[8] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x2aa;
      assert s1.Peek(9) == 0x107;
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
      assert s11.Peek(7) == 0x2aa;
      assert s11.Peek(11) == 0x107;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0x2aa;
      assert s21.Peek(11) == 0x107;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x616c616e6365);
      var s24 := Push1(s23, 0xd0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0x2aa;
      assert s31.Peek(9) == 0x107;
      var s32 := Push2(s31, 0x045a);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s33, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 83
    * Starting at 0x45a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x2aa

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2aa;
      assert s1.Peek(9) == 0x107;
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

  /** Node 65
    * Segment Id for this node is: 105
    * Starting at 0x776
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x776 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2aa

    requires s0.stack[8] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2aa;
      assert s1.Peek(8) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup5(s6);
      var s8 := And(s7);
      var s9 := Push0(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x2aa;
      assert s11.Peek(11) == 0x107;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x05);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Push2(s19, 0x0799);
      var s21 := Swap1(s20);
      assert s21.Peek(1) == 0x799;
      assert s21.Peek(6) == 0x2aa;
      assert s21.Peek(10) == 0x107;
      var s22 := Dup4(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0a49);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s25, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 146
    * Starting at 0xa49
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x799

    requires s0.stack[7] == 0x2aa

    requires s0.stack[11] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x799;
      assert s1.Peek(7) == 0x2aa;
      assert s1.Peek(11) == 0x107;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s10, gas - 1)
      else
        ExecuteFromCFGNode_s67(s10, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 147
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x799

    requires s0.stack[8] == 0x2aa

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x799;
      assert s1.Peek(9) == 0x2aa;
      assert s1.Peek(13) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s3, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x799

    requires s0.stack[9] == 0x2aa

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x799;
      assert s1.Peek(9) == 0x2aa;
      assert s1.Peek(13) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x799;
      assert s11.Peek(11) == 0x2aa;
      assert s11.Peek(15) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 69
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x799

    requires s0.stack[8] == 0x2aa

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x799;
      assert s1.Peek(8) == 0x2aa;
      assert s1.Peek(12) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s6, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 106
    * Starting at 0x799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x2aa

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2aa;
      assert s1.Peek(9) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup7(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x2aa;
      assert s11.Peek(12) == 0x107;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x05);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Keccak256(s19);
      var s21 := Swap4(s20);
      assert s21.Peek(9) == 0x2aa;
      assert s21.Peek(13) == 0x107;
      var s22 := Swap1(s21);
      var s23 := Swap4(s22);
      var s24 := SStore(s23);
      var s25 := Swap1(s24);
      var s26 := Dup6(s25);
      var s27 := And(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Keccak256(s29);
      var s31 := SLoad(s30);
      assert s31.Peek(5) == 0x2aa;
      assert s31.Peek(9) == 0x107;
      var s32 := Push2(s31, 0x07c8);
      var s33 := Swap1(s32);
      var s34 := Dup4(s33);
      var s35 := Swap1(s34);
      var s36 := Push2(s35, 0x0a36);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s37, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 144
    * Starting at 0xa36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x7c8

    requires s0.stack[7] == 0x2aa

    requires s0.stack[11] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7c8;
      assert s1.Peek(7) == 0x2aa;
      assert s1.Peek(11) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s10, gas - 1)
      else
        ExecuteFromCFGNode_s72(s10, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 145
    * Starting at 0xa42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x7c8

    requires s0.stack[8] == 0x2aa

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x7c8;
      assert s1.Peek(9) == 0x2aa;
      assert s1.Peek(13) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s3, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x7c8

    requires s0.stack[9] == 0x2aa

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x7c8;
      assert s1.Peek(9) == 0x2aa;
      assert s1.Peek(13) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x7c8;
      assert s11.Peek(11) == 0x2aa;
      assert s11.Peek(15) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 74
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x7c8

    requires s0.stack[8] == 0x2aa

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7c8;
      assert s1.Peek(8) == 0x2aa;
      assert s1.Peek(12) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s6, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 107
    * Starting at 0x7c8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x2aa

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2aa;
      assert s1.Peek(9) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup6(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(9) == 0x2aa;
      assert s11.Peek(13) == 0x107;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x05);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Dup2(s18);
      var s20 := Swap1(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(9) == 0x2aa;
      assert s21.Peek(13) == 0x107;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap2(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup7(s28);
      var s30 := And(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x2aa;
      assert s31.Peek(11) == 0x107;
      var s32 := Push32(s31, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x081b);
      var s35 := Swap1(s34);
      var s36 := Dup7(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x20);
      var s40 := Add(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s76(s41, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 108
    * Starting at 0x81a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x81b

    requires s0.stack[9] == 0x2aa

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s1, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 109
    * Starting at 0x81b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x2aa

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x2aa;
      assert s1.Peek(12) == 0x107;
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
      assert s11.Peek(1) == 0x2aa;
      assert s11.Peek(5) == 0x107;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s13, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 56
    * Starting at 0x2aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x107;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s8, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 27
    * Starting at 0x107
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107 as nat
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
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s12(s10, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 10
    * Starting at 0x63
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x70a08231);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x019a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s6, gas - 1)
      else
        ExecuteFromCFGNode_s81(s6, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 11
    * Starting at 0x6f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x715018a6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01c2);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s122(s5, gas - 1)
      else
        ExecuteFromCFGNode_s82(s5, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 12
    * Starting at 0x7a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x751039fc);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01cc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s5, gas - 1)
      else
        ExecuteFromCFGNode_s83(s5, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 13
    * Starting at 0x85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01d4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s5, gas - 1)
      else
        ExecuteFromCFGNode_s84(s5, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 14
    * Starting at 0x90
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90 as nat
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

  /** Node 85
    * Segment Id for this node is: 45
    * Starting at 0x1d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0124);
      var s3 := Push2(s2, 0x03e1);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s4, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 79
    * Starting at 0x3e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x124;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x02c2);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x09ea);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s9, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 138
    * Starting at 0x9ea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x2c2

    requires s0.stack[4] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2c2;
      assert s1.Peek(4) == 0x124;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x09fe);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s11, gas - 1)
      else
        ExecuteFromCFGNode_s88(s11, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 139
    * Starting at 0x9f8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2c2

    requires s0.stack[6] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x2c2;
      assert s1.Peek(7) == 0x124;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s89(s5, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 140
    * Starting at 0x9fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2c2

    requires s0.stack[6] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2c2;
      assert s1.Peek(6) == 0x124;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0a1c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s91(s8, gas - 1)
      else
        ExecuteFromCFGNode_s90(s8, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 141
    * Starting at 0xa09
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa09 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2c2

    requires s0.stack[6] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x2c2;
      assert s1.Peek(7) == 0x124;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 91
    * Segment Id for this node is: 142
    * Starting at 0xa1c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2c2

    requires s0.stack[6] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2c2;
      assert s1.Peek(6) == 0x124;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s6, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 58
    * Starting at 0x2c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x124;
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
      assert s11.Peek(4) == 0x124;
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
      assert s21.Peek(5) == 0x124;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x02ee);
      assert s31.Peek(0) == 0x2ee;
      assert s31.Peek(8) == 0x124;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x09ea);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s34, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 138
    * Starting at 0x9ea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x2ee

    requires s0.stack[8] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2ee;
      assert s1.Peek(8) == 0x124;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x09fe);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s11, gas - 1)
      else
        ExecuteFromCFGNode_s94(s11, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 139
    * Starting at 0x9f8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2ee

    requires s0.stack[10] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x2ee;
      assert s1.Peek(11) == 0x124;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s95(s5, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 140
    * Starting at 0x9fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2ee

    requires s0.stack[10] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ee;
      assert s1.Peek(10) == 0x124;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0a1c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s97(s8, gas - 1)
      else
        ExecuteFromCFGNode_s96(s8, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 141
    * Starting at 0xa09
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa09 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2ee

    requires s0.stack[10] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x2ee;
      assert s1.Peek(11) == 0x124;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 97
    * Segment Id for this node is: 142
    * Starting at 0xa1c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2ee

    requires s0.stack[10] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ee;
      assert s1.Peek(10) == 0x124;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s6, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 59
    * Starting at 0x2ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x124;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0339);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s5, gas - 1)
      else
        ExecuteFromCFGNode_s99(s5, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 60
    * Starting at 0x2f5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0x124;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0310);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s5, gas - 1)
      else
        ExecuteFromCFGNode_s100(s5, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 61
    * Starting at 0x2fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0x124;
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
      assert s11.Peek(7) == 0x124;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0339);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s14, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 65
    * Starting at 0x339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x124;
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
      ExecuteFromCFGNode_s102(s10, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 30
    * Starting at 0x124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0113);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x090c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s8, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 120
    * Starting at 0x90c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x113

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x113;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x113;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s104(s14, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 121
    * Starting at 0x91c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x113

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x113;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0938);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s7, gas - 1)
      else
        ExecuteFromCFGNode_s105(s7, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 122
    * Starting at 0x925
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x925 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x113

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x113;
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
      assert s11.Peek(8) == 0x113;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x091c);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s16, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 123
    * Starting at 0x938
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x938 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x113

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x113;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(7) == 0x113;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap3(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x113;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s28, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 62
    * Starting at 0x310
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x310 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x124;
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
      ExecuteFromCFGNode_s108(s11, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 63
    * Starting at 0x31c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x124;
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
      assert s11.Peek(7) == 0x124;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x031c);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s16, gas - 1)
      else
        ExecuteFromCFGNode_s109(s16, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 64
    * Starting at 0x330
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x330 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0x124;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s101(s8, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 44
    * Starting at 0x1cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01ca);
      var s3 := Push2(s2, 0x038b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s4, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 74
    * Starting at 0x38b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1ca;
      var s2 := Push1(s1, 0x04);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Sub(s10);
      assert s11.Peek(1) == 0x1ca;
      var s12 := Push2(s11, 0x0389);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s13, gas - 1)
      else
        ExecuteFromCFGNode_s112(s13, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 75
    * Starting at 0x39e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      assert s1.Peek(1) == 0x1ca;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Caller(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x03b3);
      assert s11.Peek(0) == 0x3b3;
      assert s11.Peek(2) == 0x1ca;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s12, gas - 1)
      else
        ExecuteFromCFGNode_s113(s12, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 76
    * Starting at 0x3b0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(1) == 0x1ca;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 114
    * Segment Id for this node is: 77
    * Starting at 0x3b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1ca;
      var s2 := Push1(s1, 0x09);
      var s3 := SLoad(s2);
      var s4 := Caller(s3);
      var s5 := Push0(s4);
      var s6 := Dup2(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x05);
      var s10 := Push1(s9, 0x20);
      var s11 := MStore(s10);
      assert s11.Peek(3) == 0x1ca;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup2(s12);
      var s14 := Keccak256(s13);
      var s15 := Dup1(s14);
      var s16 := SLoad(s15);
      var s17 := Swap3(s16);
      var s18 := Swap4(s17);
      var s19 := Dup5(s18);
      var s20 := Swap4(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(6) == 0x1ca;
      var s22 := Swap3(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x03d8);
      var s25 := Swap1(s24);
      var s26 := Dup5(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x0a36);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s29, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 144
    * Starting at 0xa36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x3d8

    requires s0.stack[8] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3d8;
      assert s1.Peek(8) == 0x1ca;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s10, gas - 1)
      else
        ExecuteFromCFGNode_s116(s10, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 145
    * Starting at 0xa42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3d8

    requires s0.stack[9] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x3d8;
      assert s1.Peek(10) == 0x1ca;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s3, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x3d8

    requires s0.stack[10] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x3d8;
      assert s1.Peek(10) == 0x1ca;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x3d8;
      assert s11.Peek(12) == 0x1ca;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 118
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3d8

    requires s0.stack[9] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d8;
      assert s1.Peek(9) == 0x1ca;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s6, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 78
    * Starting at 0x3d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1ca;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s9, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 43
    * Starting at 0x1ca
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ca as nat
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

  /** Node 121
    * Segment Id for this node is: 73
    * Starting at 0x389
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x389 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1ca;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s2, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 42
    * Starting at 0x1c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01ca);
      var s3 := Push2(s2, 0x0378);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s4, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 71
    * Starting at 0x378
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x378 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1ca;
      var s2 := Push2(s1, 0x0380);
      var s3 := Push2(s2, 0x0829);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s4, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 110
    * Starting at 0x829
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x829 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x380

    requires s0.stack[1] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x380;
      assert s1.Peek(1) == 0x1ca;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x380;
      assert s11.Peek(2) == 0x1ca;
      var s12 := Push2(s11, 0x0389);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s13, gas - 1)
      else
        ExecuteFromCFGNode_s125(s13, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 111
    * Starting at 0x83b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x380

    requires s0.stack[1] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x380;
      assert s1.Peek(2) == 0x1ca;
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
      assert s11.Peek(3) == 0x380;
      assert s11.Peek(4) == 0x1ca;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f74207468652061646d696e);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x380;
      assert s21.Peek(5) == 0x1ca;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x045a);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s27, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 83
    * Starting at 0x45a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x380

    requires s0.stack[2] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x380;
      assert s1.Peek(2) == 0x1ca;
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

  /** Node 127
    * Segment Id for this node is: 73
    * Starting at 0x389
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x389 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x380

    requires s0.stack[1] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x380;
      assert s1.Peek(1) == 0x1ca;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s2, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 72
    * Starting at 0x380
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x380 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1ca;
      var s2 := Push2(s1, 0x0389);
      var s3 := Push0(s2);
      var s4 := Push2(s3, 0x0882);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s5, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 112
    * Starting at 0x882
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x882 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x389

    requires s0.stack[2] == 0x1ca

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x389;
      assert s1.Peek(2) == 0x1ca;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup4(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x389;
      assert s11.Peek(7) == 0x1ca;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Not(s17);
      var s19 := Dup4(s18);
      var s20 := And(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(7) == 0x389;
      assert s21.Peek(8) == 0x1ca;
      var s22 := Or(s21);
      var s23 := Dup5(s22);
      var s24 := SStore(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Swap2(s26);
      var s28 := Swap1(s27);
      var s29 := Swap3(s28);
      var s30 := And(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(5) == 0x389;
      assert s31.Peek(6) == 0x1ca;
      var s32 := Dup4(s31);
      var s33 := Swap2(s32);
      var s34 := Push32(s33, 0xfc8eccee73d2808082db1cc1e48f1ba2d1e9585ac72363bb1f939c9cb8c20ea3);
      var s35 := Swap2(s34);
      var s36 := Swap1(s35);
      var s37 := Log3(s36);
      var s38 := Pop(s37);
      var s39 := Pop(s38);
      var s40 := Jump(s39);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s40, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 40
    * Starting at 0x19a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x016a);
      var s3 := Push2(s2, 0x01a8);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x08ec);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s7, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 116
    * Starting at 0x8ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1a8

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1a8;
      assert s1.Peek(3) == 0x16a;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x08fc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s10, gas - 1)
      else
        ExecuteFromCFGNode_s132(s10, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 117
    * Starting at 0x8f9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1a8

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x1a8;
      assert s1.Peek(5) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 133
    * Segment Id for this node is: 118
    * Starting at 0x8fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1a8

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1a8;
      assert s1.Peek(4) == 0x16a;
      var s2 := Push2(s1, 0x0905);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x08d1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s5, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 113
    * Starting at 0x8d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x905

    requires s0.stack[5] == 0x1a8

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x905;
      assert s1.Peek(5) == 0x1a8;
      assert s1.Peek(6) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x905;
      assert s11.Peek(8) == 0x1a8;
      assert s11.Peek(9) == 0x16a;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x08e7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s14, gas - 1)
      else
        ExecuteFromCFGNode_s135(s14, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 114
    * Starting at 0x8e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x905

    requires s0.stack[6] == 0x1a8

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x905;
      assert s1.Peek(7) == 0x1a8;
      assert s1.Peek(8) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 136
    * Segment Id for this node is: 115
    * Starting at 0x8e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x905

    requires s0.stack[6] == 0x1a8

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x905;
      assert s1.Peek(6) == 0x1a8;
      assert s1.Peek(7) == 0x16a;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s5, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 119
    * Starting at 0x905
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x905 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1a8

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1a8;
      assert s1.Peek(5) == 0x16a;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s7, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 41
    * Starting at 0x1a8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x16a;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push0(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x16a;
      var s12 := Push1(s11, 0x05);
      var s13 := Push1(s12, 0x20);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Swap1(s15);
      var s17 := Keccak256(s16);
      var s18 := SLoad(s17);
      var s19 := Swap1(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s20, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 15
    * Starting at 0x93
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x0acac942);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00ce);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s6, gas - 1)
      else
        ExecuteFromCFGNode_s140(s6, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 16
    * Starting at 0x9f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x0acac942);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0144);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s219(s5, gas - 1)
      else
        ExecuteFromCFGNode_s141(s5, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 17
    * Starting at 0xaa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0166);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s5, gas - 1)
      else
        ExecuteFromCFGNode_s142(s5, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 18
    * Starting at 0xb5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0178);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s146(s5, gas - 1)
      else
        ExecuteFromCFGNode_s143(s5, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 19
    * Starting at 0xc0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x018b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s5, gas - 1)
      else
        ExecuteFromCFGNode_s144(s5, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 20
    * Starting at 0xcb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb as nat
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

  /** Node 145
    * Segment Id for this node is: 39
    * Starting at 0x18b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x12);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0113);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s10, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 37
    * Starting at 0x178
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x178 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0107);
      var s3 := Push2(s2, 0x0186);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0980);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s7, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 128
    * Starting at 0x980
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x980 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x186

    requires s0.stack[3] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x186;
      assert s1.Peek(3) == 0x107;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0992);
      assert s11.Peek(0) == 0x992;
      assert s11.Peek(7) == 0x186;
      assert s11.Peek(8) == 0x107;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s12, gas - 1)
      else
        ExecuteFromCFGNode_s148(s12, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 129
    * Starting at 0x98f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x186

    requires s0.stack[6] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x186;
      assert s1.Peek(7) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 149
    * Segment Id for this node is: 130
    * Starting at 0x992
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x992 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x186

    requires s0.stack[6] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x186;
      assert s1.Peek(6) == 0x107;
      var s2 := Push2(s1, 0x099b);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x08d1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s5, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 113
    * Starting at 0x8d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x99b

    requires s0.stack[7] == 0x186

    requires s0.stack[8] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x99b;
      assert s1.Peek(7) == 0x186;
      assert s1.Peek(8) == 0x107;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x99b;
      assert s11.Peek(10) == 0x186;
      assert s11.Peek(11) == 0x107;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x08e7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s14, gas - 1)
      else
        ExecuteFromCFGNode_s151(s14, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 114
    * Starting at 0x8e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x99b

    requires s0.stack[8] == 0x186

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x99b;
      assert s1.Peek(9) == 0x186;
      assert s1.Peek(10) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 152
    * Segment Id for this node is: 115
    * Starting at 0x8e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x99b

    requires s0.stack[8] == 0x186

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x99b;
      assert s1.Peek(8) == 0x186;
      assert s1.Peek(9) == 0x107;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s5, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 131
    * Starting at 0x99b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x186

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x186;
      assert s1.Peek(7) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x09a9);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x08d1);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s9, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 113
    * Starting at 0x8d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x9a9

    requires s0.stack[7] == 0x186

    requires s0.stack[8] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9a9;
      assert s1.Peek(7) == 0x186;
      assert s1.Peek(8) == 0x107;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x9a9;
      assert s11.Peek(10) == 0x186;
      assert s11.Peek(11) == 0x107;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x08e7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s14, gas - 1)
      else
        ExecuteFromCFGNode_s155(s14, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 114
    * Starting at 0x8e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x9a9

    requires s0.stack[8] == 0x186

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x9a9;
      assert s1.Peek(9) == 0x186;
      assert s1.Peek(10) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 156
    * Segment Id for this node is: 115
    * Starting at 0x8e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x9a9

    requires s0.stack[8] == 0x186

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9a9;
      assert s1.Peek(8) == 0x186;
      assert s1.Peek(9) == 0x107;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s5, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 132
    * Starting at 0x9a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x186

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x186;
      assert s1.Peek(7) == 0x107;
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
      assert s11.Peek(4) == 0x186;
      assert s11.Peek(5) == 0x107;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Swap3(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s15, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 38
    * Starting at 0x186
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x186 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x107;
      var s2 := Push2(s1, 0x0355);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s3, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 68
    * Starting at 0x355
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x355 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x107;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Push2(s3, 0x0362);
      var s5 := Dup6(s4);
      var s6 := Dup3(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x0524);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s9, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 88
    * Starting at 0x524
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x524 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x362

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x362;
      assert s1.Peek(9) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0x362;
      assert s11.Peek(12) == 0x107;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x06);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(9) == 0x362;
      assert s21.Peek(15) == 0x107;
      var s22 := Keccak256(s21);
      var s23 := Swap4(s22);
      var s24 := Dup7(s23);
      var s25 := And(s24);
      var s26 := Dup4(s25);
      var s27 := MStore(s26);
      var s28 := Swap3(s27);
      var s29 := Swap1(s28);
      var s30 := MStore(s29);
      var s31 := Keccak256(s30);
      assert s31.Peek(4) == 0x362;
      assert s31.Peek(10) == 0x107;
      var s32 := SLoad(s31);
      var s33 := Push0(s32);
      var s34 := Not(s33);
      var s35 := Dup2(s34);
      var s36 := Eq(s35);
      var s37 := Push2(s36, 0x05b5);
      var s38 := JumpI(s37);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s37.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s38, gas - 1)
      else
        ExecuteFromCFGNode_s161(s38, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 89
    * Starting at 0x552
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x552 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x362

    requires s0.stack[10] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x362;
      assert s1.Peek(11) == 0x107;
      var s2 := Dup2(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x05a1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s6, gas - 1)
      else
        ExecuteFromCFGNode_s162(s6, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 90
    * Starting at 0x55a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x362

    requires s0.stack[10] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x362;
      assert s1.Peek(11) == 0x107;
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
      assert s11.Peek(7) == 0x362;
      assert s11.Peek(13) == 0x107;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a20696e73756666696369656e7420616c6c6f77616e6365000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0x362;
      assert s21.Peek(13) == 0x107;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x045a);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s26, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 83
    * Starting at 0x45a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x362

    requires s0.stack[11] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x362;
      assert s1.Peek(11) == 0x107;
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

  /** Node 164
    * Segment Id for this node is: 91
    * Starting at 0x5a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x362

    requires s0.stack[10] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x362;
      assert s1.Peek(10) == 0x107;
      var s2 := Push2(s1, 0x05b5);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Push2(s4, 0x05b0);
      var s6 := Dup6(s5);
      var s7 := Dup6(s6);
      var s8 := Push2(s7, 0x0a49);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s9, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 146
    * Starting at 0xa49
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x5b0

    requires s0.stack[5] == 0x5b5

    requires s0.stack[10] == 0x362

    requires s0.stack[16] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5b0;
      assert s1.Peek(5) == 0x5b5;
      assert s1.Peek(10) == 0x362;
      assert s1.Peek(16) == 0x107;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s168(s10, gas - 1)
      else
        ExecuteFromCFGNode_s166(s10, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 147
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x5b0

    requires s0.stack[6] == 0x5b5

    requires s0.stack[11] == 0x362

    requires s0.stack[17] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x5b0;
      assert s1.Peek(7) == 0x5b5;
      assert s1.Peek(12) == 0x362;
      assert s1.Peek(18) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s3, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x5b0

    requires s0.stack[7] == 0x5b5

    requires s0.stack[12] == 0x362

    requires s0.stack[18] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x5b0;
      assert s1.Peek(7) == 0x5b5;
      assert s1.Peek(12) == 0x362;
      assert s1.Peek(18) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x5b0;
      assert s11.Peek(9) == 0x5b5;
      assert s11.Peek(14) == 0x362;
      assert s11.Peek(20) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 168
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x5b0

    requires s0.stack[6] == 0x5b5

    requires s0.stack[11] == 0x362

    requires s0.stack[17] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b0;
      assert s1.Peek(6) == 0x5b5;
      assert s1.Peek(11) == 0x362;
      assert s1.Peek(17) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s6, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 92
    * Starting at 0x5b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x5b5

    requires s0.stack[8] == 0x362

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b5;
      assert s1.Peek(8) == 0x362;
      assert s1.Peek(14) == 0x107;
      var s2 := Push2(s1, 0x03fc);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s3, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 81
    * Starting at 0x3fc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x5b5

    requires s0.stack[8] == 0x362

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b5;
      assert s1.Peek(8) == 0x362;
      assert s1.Peek(14) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0463);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s173(s10, gas - 1)
      else
        ExecuteFromCFGNode_s171(s10, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 82
    * Starting at 0x40b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x5b5

    requires s0.stack[8] == 0x362

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5b5;
      assert s1.Peek(9) == 0x362;
      assert s1.Peek(15) == 0x107;
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
      assert s11.Peek(6) == 0x5b5;
      assert s11.Peek(11) == 0x362;
      assert s11.Peek(17) == 0x107;
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
      assert s21.Peek(6) == 0x5b5;
      assert s21.Peek(11) == 0x362;
      assert s21.Peek(17) == 0x107;
      var s22 := MStore(s21);
      var s23 := Push4(s22, 0x72657373);
      var s24 := Push1(s23, 0xe0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s172(s31, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 83
    * Starting at 0x45a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x5b5

    requires s0.stack[9] == 0x362

    requires s0.stack[15] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5b5;
      assert s1.Peek(9) == 0x362;
      assert s1.Peek(15) == 0x107;
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

  /** Node 173
    * Segment Id for this node is: 84
    * Starting at 0x463
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x5b5

    requires s0.stack[8] == 0x362

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b5;
      assert s1.Peek(8) == 0x362;
      assert s1.Peek(14) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x04c4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s10, gas - 1)
      else
        ExecuteFromCFGNode_s174(s10, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 85
    * Starting at 0x472
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x472 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x5b5

    requires s0.stack[8] == 0x362

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5b5;
      assert s1.Peek(9) == 0x362;
      assert s1.Peek(15) == 0x107;
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
      assert s11.Peek(6) == 0x5b5;
      assert s11.Peek(11) == 0x362;
      assert s11.Peek(17) == 0x107;
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
      assert s21.Peek(6) == 0x5b5;
      assert s21.Peek(11) == 0x362;
      assert s21.Peek(17) == 0x107;
      var s22 := MStore(s21);
      var s23 := Push2(s22, 0x7373);
      var s24 := Push1(s23, 0xf0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x5b5;
      assert s31.Peek(9) == 0x362;
      assert s31.Peek(15) == 0x107;
      var s32 := Push2(s31, 0x045a);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s33, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 86
    * Starting at 0x4c4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x5b5

    requires s0.stack[8] == 0x362

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b5;
      assert s1.Peek(8) == 0x362;
      assert s1.Peek(14) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x5b5;
      assert s11.Peek(12) == 0x362;
      assert s11.Peek(18) == 0x107;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x06);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x5b5;
      assert s21.Peek(15) == 0x362;
      assert s21.Peek(21) == 0x107;
      var s22 := Keccak256(s21);
      var s23 := Swap5(s22);
      var s24 := Dup8(s23);
      var s25 := And(s24);
      var s26 := Dup1(s25);
      var s27 := Dup5(s26);
      var s28 := MStore(s27);
      var s29 := Swap5(s28);
      var s30 := Dup3(s29);
      var s31 := MStore(s30);
      assert s31.Peek(8) == 0x5b5;
      assert s31.Peek(13) == 0x362;
      assert s31.Peek(19) == 0x107;
      var s32 := Swap2(s31);
      var s33 := Dup3(s32);
      var s34 := Swap1(s33);
      var s35 := Keccak256(s34);
      var s36 := Dup6(s35);
      var s37 := Swap1(s36);
      var s38 := SStore(s37);
      var s39 := Swap1(s38);
      var s40 := MLoad(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s176(s41, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 87
    * Starting at 0x4f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0x5b5

    requires s0.stack[13] == 0x362

    requires s0.stack[19] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x5b5;
      assert s1.Peek(14) == 0x362;
      assert s1.Peek(20) == 0x107;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Swap2(s8);
      var s10 := Sub(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x5b5;
      assert s11.Peek(13) == 0x362;
      assert s11.Peek(19) == 0x107;
      var s12 := Log3(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s16, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 93
    * Starting at 0x5b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x362

    requires s0.stack[10] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x362;
      assert s1.Peek(10) == 0x107;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s6, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 69
    * Starting at 0x362
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x362 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x107;
      var s2 := Push2(s1, 0x036d);
      var s3 := Dup6(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Push2(s5, 0x05bb);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s7, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 94
    * Starting at 0x5bb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x36d

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x36d;
      assert s1.Peek(9) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x061f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s10, gas - 1)
      else
        ExecuteFromCFGNode_s180(s10, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 95
    * Starting at 0x5ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x36d

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x36d;
      assert s1.Peek(10) == 0x107;
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
      assert s11.Peek(6) == 0x36d;
      assert s11.Peek(12) == 0x107;
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
      assert s21.Peek(6) == 0x36d;
      assert s21.Peek(12) == 0x107;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 5, 0x6472657373);
      var s24 := Push1(s23, 0xd8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x36d;
      assert s31.Peek(10) == 0x107;
      var s32 := Push2(s31, 0x045a);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s33, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 83
    * Starting at 0x45a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x36d

    requires s0.stack[10] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x36d;
      assert s1.Peek(10) == 0x107;
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

  /** Node 182
    * Segment Id for this node is: 96
    * Starting at 0x61f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x36d

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x36d;
      assert s1.Peek(9) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0681);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s184(s10, gas - 1)
      else
        ExecuteFromCFGNode_s183(s10, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 97
    * Starting at 0x62e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x36d

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x36d;
      assert s1.Peek(10) == 0x107;
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
      assert s11.Peek(6) == 0x36d;
      assert s11.Peek(12) == 0x107;
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
      assert s21.Peek(6) == 0x36d;
      assert s21.Peek(12) == 0x107;
      var s22 := MStore(s21);
      var s23 := Push3(s22, 0x657373);
      var s24 := Push1(s23, 0xe8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x36d;
      assert s31.Peek(10) == 0x107;
      var s32 := Push2(s31, 0x045a);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s33, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 98
    * Starting at 0x681
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x681 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x36d

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x36d;
      assert s1.Peek(9) == 0x107;
      var s2 := Push1(s1, 0x0a);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := And(s9);
      var s11 := Push0(s10);
      assert s11.Peek(6) == 0x36d;
      assert s11.Peek(12) == 0x107;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x07);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap1(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x36d;
      assert s21.Peek(11) == 0x107;
      var s22 := Push1(s21, 0xff);
      var s23 := Swap2(s22);
      var s24 := Dup3(s23);
      var s25 := And(s24);
      var s26 := IsZero(s25);
      var s27 := IsZero(s26);
      var s28 := Swap2(s27);
      var s29 := And(s28);
      var s30 := IsZero(s29);
      var s31 := IsZero(s30);
      assert s31.Peek(5) == 0x36d;
      assert s31.Peek(11) == 0x107;
      var s32 := Sub(s31);
      var s33 := Push2(s32, 0x06ff);
      var s34 := JumpI(s33);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s33.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s34, gas - 1)
      else
        ExecuteFromCFGNode_s185(s34, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 99
    * Starting at 0x6ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x36d

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x08);
      assert s1.Peek(4) == 0x36d;
      assert s1.Peek(10) == 0x107;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup5(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0x36d;
      assert s11.Peek(12) == 0x107;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x05);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Keccak256(s18);
      var s20 := SLoad(s19);
      var s21 := PushN(s20, 16, 0xffffffffffffffffffffffffffffffff);
      assert s21.Peek(6) == 0x36d;
      assert s21.Peek(12) == 0x107;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := And(s23);
      var s25 := Swap1(s24);
      var s26 := Dup2(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x06e8);
      var s29 := Swap1(s28);
      var s30 := Dup3(s29);
      var s31 := Push2(s30, 0x0a36);
      assert s31.Peek(0) == 0xa36;
      assert s31.Peek(3) == 0x6e8;
      assert s31.Peek(9) == 0x36d;
      assert s31.Peek(15) == 0x107;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s32, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 144
    * Starting at 0xa36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x6e8

    requires s0.stack[8] == 0x36d

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6e8;
      assert s1.Peek(8) == 0x36d;
      assert s1.Peek(14) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s10, gas - 1)
      else
        ExecuteFromCFGNode_s187(s10, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 145
    * Starting at 0xa42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x6e8

    requires s0.stack[9] == 0x36d

    requires s0.stack[15] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6e8;
      assert s1.Peek(10) == 0x36d;
      assert s1.Peek(16) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s3, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x6e8

    requires s0.stack[10] == 0x36d

    requires s0.stack[16] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6e8;
      assert s1.Peek(10) == 0x36d;
      assert s1.Peek(16) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x6e8;
      assert s11.Peek(12) == 0x36d;
      assert s11.Peek(18) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 189
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x6e8

    requires s0.stack[9] == 0x36d

    requires s0.stack[15] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6e8;
      assert s1.Peek(9) == 0x36d;
      assert s1.Peek(15) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s6, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 100
    * Starting at 0x6e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x36d

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x36d;
      assert s1.Peek(12) == 0x107;
      var s2 := Push2(s1, 0x06f2);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0a36);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s6, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 144
    * Starting at 0xa36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x6f2

    requires s0.stack[7] == 0x36d

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6f2;
      assert s1.Peek(7) == 0x36d;
      assert s1.Peek(13) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s10, gas - 1)
      else
        ExecuteFromCFGNode_s192(s10, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 145
    * Starting at 0xa42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x6f2

    requires s0.stack[8] == 0x36d

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6f2;
      assert s1.Peek(9) == 0x36d;
      assert s1.Peek(15) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s3, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x6f2

    requires s0.stack[9] == 0x36d

    requires s0.stack[15] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6f2;
      assert s1.Peek(9) == 0x36d;
      assert s1.Peek(15) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x6f2;
      assert s11.Peek(11) == 0x36d;
      assert s11.Peek(17) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 194
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x6f2

    requires s0.stack[8] == 0x36d

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6f2;
      assert s1.Peek(8) == 0x36d;
      assert s1.Peek(14) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s6, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 101
    * Starting at 0x6f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x36d

    requires s0.stack[11] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x36d;
      assert s1.Peek(11) == 0x107;
      var s2 := Push2(s1, 0x06fc);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0a49);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s6, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 146
    * Starting at 0xa49
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x6fc

    requires s0.stack[6] == 0x36d

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6fc;
      assert s1.Peek(6) == 0x36d;
      assert s1.Peek(12) == 0x107;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s10, gas - 1)
      else
        ExecuteFromCFGNode_s197(s10, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 147
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x6fc

    requires s0.stack[7] == 0x36d

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6fc;
      assert s1.Peek(8) == 0x36d;
      assert s1.Peek(14) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s3, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x6fc

    requires s0.stack[8] == 0x36d

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x6fc;
      assert s1.Peek(8) == 0x36d;
      assert s1.Peek(14) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x6fc;
      assert s11.Peek(10) == 0x36d;
      assert s11.Peek(16) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 199
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x6fc

    requires s0.stack[7] == 0x36d

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6fc;
      assert s1.Peek(7) == 0x36d;
      assert s1.Peek(13) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s6, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 102
    * Starting at 0x6fc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x36d

    requires s0.stack[10] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x36d;
      assert s1.Peek(10) == 0x107;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s201(s3, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 103
    * Starting at 0x6ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x36d

    requires s0.stack[9] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x36d;
      assert s1.Peek(9) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push0(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x36d;
      assert s11.Peek(12) == 0x107;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x05);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Dup2(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x36d;
      assert s21.Peek(12) == 0x107;
      var s22 := Lt(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x0776);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s25, gas - 1)
      else
        ExecuteFromCFGNode_s202(s25, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 104
    * Starting at 0x720
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x720 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x36d

    requires s0.stack[10] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x36d;
      assert s1.Peek(11) == 0x107;
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
      assert s11.Peek(7) == 0x36d;
      assert s11.Peek(13) == 0x107;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0x36d;
      assert s21.Peek(13) == 0x107;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x616c616e6365);
      var s24 := Push1(s23, 0xd0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0x36d;
      assert s31.Peek(11) == 0x107;
      var s32 := Push2(s31, 0x045a);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s33, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 83
    * Starting at 0x45a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x36d

    requires s0.stack[11] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x36d;
      assert s1.Peek(11) == 0x107;
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

  /** Node 204
    * Segment Id for this node is: 105
    * Starting at 0x776
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x776 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x36d

    requires s0.stack[10] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x36d;
      assert s1.Peek(10) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup5(s6);
      var s8 := And(s7);
      var s9 := Push0(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x36d;
      assert s11.Peek(13) == 0x107;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x05);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Push2(s19, 0x0799);
      var s21 := Swap1(s20);
      assert s21.Peek(1) == 0x799;
      assert s21.Peek(6) == 0x36d;
      assert s21.Peek(12) == 0x107;
      var s22 := Dup4(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0a49);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s25, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 146
    * Starting at 0xa49
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x799

    requires s0.stack[7] == 0x36d

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x799;
      assert s1.Peek(7) == 0x36d;
      assert s1.Peek(13) == 0x107;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s208(s10, gas - 1)
      else
        ExecuteFromCFGNode_s206(s10, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 147
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x799

    requires s0.stack[8] == 0x36d

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x799;
      assert s1.Peek(9) == 0x36d;
      assert s1.Peek(15) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s3, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x799

    requires s0.stack[9] == 0x36d

    requires s0.stack[15] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x799;
      assert s1.Peek(9) == 0x36d;
      assert s1.Peek(15) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x799;
      assert s11.Peek(11) == 0x36d;
      assert s11.Peek(17) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 208
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x799

    requires s0.stack[8] == 0x36d

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x799;
      assert s1.Peek(8) == 0x36d;
      assert s1.Peek(14) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s6, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 106
    * Starting at 0x799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x36d

    requires s0.stack[11] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x36d;
      assert s1.Peek(11) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup7(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x36d;
      assert s11.Peek(14) == 0x107;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x05);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Keccak256(s19);
      var s21 := Swap4(s20);
      assert s21.Peek(9) == 0x36d;
      assert s21.Peek(15) == 0x107;
      var s22 := Swap1(s21);
      var s23 := Swap4(s22);
      var s24 := SStore(s23);
      var s25 := Swap1(s24);
      var s26 := Dup6(s25);
      var s27 := And(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Keccak256(s29);
      var s31 := SLoad(s30);
      assert s31.Peek(5) == 0x36d;
      assert s31.Peek(11) == 0x107;
      var s32 := Push2(s31, 0x07c8);
      var s33 := Swap1(s32);
      var s34 := Dup4(s33);
      var s35 := Swap1(s34);
      var s36 := Push2(s35, 0x0a36);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s37, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 144
    * Starting at 0xa36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x7c8

    requires s0.stack[7] == 0x36d

    requires s0.stack[13] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7c8;
      assert s1.Peek(7) == 0x36d;
      assert s1.Peek(13) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s213(s10, gas - 1)
      else
        ExecuteFromCFGNode_s211(s10, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 145
    * Starting at 0xa42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x7c8

    requires s0.stack[8] == 0x36d

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x034f);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x7c8;
      assert s1.Peek(9) == 0x36d;
      assert s1.Peek(15) == 0x107;
      var s2 := Push2(s1, 0x0a22);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s3, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 143
    * Starting at 0xa22
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x34f

    requires s0.stack[4] == 0x7c8

    requires s0.stack[9] == 0x36d

    requires s0.stack[15] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x34f;
      assert s1.Peek(4) == 0x7c8;
      assert s1.Peek(9) == 0x36d;
      assert s1.Peek(15) == 0x107;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x34f;
      assert s11.Peek(6) == 0x7c8;
      assert s11.Peek(11) == 0x36d;
      assert s11.Peek(17) == 0x107;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 213
    * Segment Id for this node is: 67
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x7c8

    requires s0.stack[8] == 0x36d

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7c8;
      assert s1.Peek(8) == 0x36d;
      assert s1.Peek(14) == 0x107;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s6, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 107
    * Starting at 0x7c8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x36d

    requires s0.stack[11] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x36d;
      assert s1.Peek(11) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup6(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(9) == 0x36d;
      assert s11.Peek(15) == 0x107;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x05);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Dup2(s18);
      var s20 := Swap1(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(9) == 0x36d;
      assert s21.Peek(15) == 0x107;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap2(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup7(s28);
      var s30 := And(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x36d;
      assert s31.Peek(13) == 0x107;
      var s32 := Push32(s31, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x081b);
      var s35 := Swap1(s34);
      var s36 := Dup7(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x20);
      var s40 := Add(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s215(s41, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 108
    * Starting at 0x81a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x81b

    requires s0.stack[9] == 0x36d

    requires s0.stack[15] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s1, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 109
    * Starting at 0x81b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x36d

    requires s0.stack[14] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x36d;
      assert s1.Peek(14) == 0x107;
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
      assert s11.Peek(1) == 0x36d;
      assert s11.Peek(7) == 0x107;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s13, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 70
    * Starting at 0x36d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x107;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap5(s3);
      var s5 := Swap4(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s10, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 35
    * Starting at 0x166
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x166 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x03);
      var s3 := SLoad(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s26(s3, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 33
    * Starting at 0x144
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x144 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0107);
      var s3 := Push2(s2, 0x0152);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x08ec);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s7, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 116
    * Starting at 0x8ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x152

    requires s0.stack[3] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x152;
      assert s1.Peek(3) == 0x107;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x08fc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s222(s10, gas - 1)
      else
        ExecuteFromCFGNode_s221(s10, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 117
    * Starting at 0x8f9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x152

    requires s0.stack[4] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x152;
      assert s1.Peek(5) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 222
    * Segment Id for this node is: 118
    * Starting at 0x8fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x152

    requires s0.stack[4] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x152;
      assert s1.Peek(4) == 0x107;
      var s2 := Push2(s1, 0x0905);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x08d1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s5, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 113
    * Starting at 0x8d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x905

    requires s0.stack[5] == 0x152

    requires s0.stack[6] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x905;
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(6) == 0x107;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x905;
      assert s11.Peek(8) == 0x152;
      assert s11.Peek(9) == 0x107;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x08e7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s225(s14, gas - 1)
      else
        ExecuteFromCFGNode_s224(s14, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 114
    * Starting at 0x8e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x905

    requires s0.stack[6] == 0x152

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x905;
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(8) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 225
    * Segment Id for this node is: 115
    * Starting at 0x8e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x905

    requires s0.stack[6] == 0x152

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x905;
      assert s1.Peek(6) == 0x152;
      assert s1.Peek(7) == 0x107;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s5, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 119
    * Starting at 0x905
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x905 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x152

    requires s0.stack[5] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x152;
      assert s1.Peek(5) == 0x107;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s7, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 34
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x107;
      var s2 := Push1(s1, 0x07);
      var s3 := Push1(s2, 0x20);
      var s4 := MStore(s3);
      var s5 := Push0(s4);
      var s6 := Swap1(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x107;
      var s12 := SLoad(s11);
      var s13 := Push1(s12, 0xff);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s16, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 27
    * Starting at 0x107
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x107;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s229(s10, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 28
    * Starting at 0x113
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x107;
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

  /** Node 230
    * Segment Id for this node is: 21
    * Starting at 0xce
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x03438dd0);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00f4);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s252(s6, gas - 1)
      else
        ExecuteFromCFGNode_s231(s6, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 22
    * Starting at 0xda
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x06fdde03);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x011c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s250(s5, gas - 1)
      else
        ExecuteFromCFGNode_s232(s5, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 23
    * Starting at 0xe5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0131);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s234(s5, gas - 1)
      else
        ExecuteFromCFGNode_s233(s5, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 24
    * Starting at 0xf0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0 as nat
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

  /** Node 234
    * Segment Id for this node is: 31
    * Starting at 0x131
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0107);
      var s3 := Push2(s2, 0x013f);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0958);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s7, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 124
    * Starting at 0x958
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x958 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x13f

    requires s0.stack[3] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13f;
      assert s1.Peek(3) == 0x107;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0969);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s237(s11, gas - 1)
      else
        ExecuteFromCFGNode_s236(s11, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 125
    * Starting at 0x966
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x966 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x13f

    requires s0.stack[5] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x13f;
      assert s1.Peek(6) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 237
    * Segment Id for this node is: 126
    * Starting at 0x969
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x969 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x13f

    requires s0.stack[5] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x13f;
      assert s1.Peek(5) == 0x107;
      var s2 := Push2(s1, 0x0972);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x08d1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s5, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 113
    * Starting at 0x8d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x972

    requires s0.stack[6] == 0x13f

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x972;
      assert s1.Peek(6) == 0x13f;
      assert s1.Peek(7) == 0x107;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x972;
      assert s11.Peek(9) == 0x13f;
      assert s11.Peek(10) == 0x107;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x08e7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s14, gas - 1)
      else
        ExecuteFromCFGNode_s239(s14, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 114
    * Starting at 0x8e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x972

    requires s0.stack[7] == 0x13f

    requires s0.stack[8] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x972;
      assert s1.Peek(8) == 0x13f;
      assert s1.Peek(9) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 240
    * Segment Id for this node is: 115
    * Starting at 0x8e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x972

    requires s0.stack[7] == 0x13f

    requires s0.stack[8] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x972;
      assert s1.Peek(7) == 0x13f;
      assert s1.Peek(8) == 0x107;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s5, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 127
    * Starting at 0x972
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x972 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x13f

    requires s0.stack[6] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x13f;
      assert s1.Peek(6) == 0x107;
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
      assert s11.Peek(1) == 0x13f;
      assert s11.Peek(4) == 0x107;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s13, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 32
    * Starting at 0x13f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x107;
      var s2 := Push2(s1, 0x0343);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s3, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 66
    * Starting at 0x343
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x343 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x107;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02aa);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x03fc);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s8, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 81
    * Starting at 0x3fc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2aa;
      assert s1.Peek(7) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0463);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s246(s10, gas - 1)
      else
        ExecuteFromCFGNode_s245(s10, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 82
    * Starting at 0x40b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2aa;
      assert s1.Peek(8) == 0x107;
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
      assert s11.Peek(6) == 0x2aa;
      assert s11.Peek(10) == 0x107;
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
      assert s21.Peek(6) == 0x2aa;
      assert s21.Peek(10) == 0x107;
      var s22 := MStore(s21);
      var s23 := Push4(s22, 0x72657373);
      var s24 := Push1(s23, 0xe0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s42(s31, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 84
    * Starting at 0x463
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x463 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2aa;
      assert s1.Peek(7) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x04c4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s10, gas - 1)
      else
        ExecuteFromCFGNode_s247(s10, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 85
    * Starting at 0x472
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x472 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2aa;
      assert s1.Peek(8) == 0x107;
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
      assert s11.Peek(6) == 0x2aa;
      assert s11.Peek(10) == 0x107;
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
      assert s21.Peek(6) == 0x2aa;
      assert s21.Peek(10) == 0x107;
      var s22 := MStore(s21);
      var s23 := Push2(s22, 0x7373);
      var s24 := Push1(s23, 0xf0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x2aa;
      assert s31.Peek(8) == 0x107;
      var s32 := Push2(s31, 0x045a);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s33, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 86
    * Starting at 0x4c4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2aa

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2aa;
      assert s1.Peek(7) == 0x107;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x2aa;
      assert s11.Peek(11) == 0x107;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x06);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x2aa;
      assert s21.Peek(14) == 0x107;
      var s22 := Keccak256(s21);
      var s23 := Swap5(s22);
      var s24 := Dup8(s23);
      var s25 := And(s24);
      var s26 := Dup1(s25);
      var s27 := Dup5(s26);
      var s28 := MStore(s27);
      var s29 := Swap5(s28);
      var s30 := Dup3(s29);
      var s31 := MStore(s30);
      assert s31.Peek(8) == 0x2aa;
      assert s31.Peek(12) == 0x107;
      var s32 := Swap2(s31);
      var s33 := Dup3(s32);
      var s34 := Swap1(s33);
      var s35 := Keccak256(s34);
      var s36 := Dup6(s35);
      var s37 := Swap1(s36);
      var s38 := SStore(s37);
      var s39 := Swap1(s38);
      var s40 := MLoad(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s249(s41, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 87
    * Starting at 0x4f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x2aa

    requires s0.stack[12] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x2aa;
      assert s1.Peek(13) == 0x107;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Swap2(s8);
      var s10 := Sub(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x2aa;
      assert s11.Peek(12) == 0x107;
      var s12 := Log3(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s16, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 29
    * Starting at 0x11c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0124);
      var s3 := Push2(s2, 0x02b3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s4, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 57
    * Starting at 0x2b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x124

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x124;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x02c2);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x09ea);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s9, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 25
    * Starting at 0xf4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0107);
      var s3 := Push2(s2, 0x0102);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x08ec);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s7, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 116
    * Starting at 0x8ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x102

    requires s0.stack[3] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x102;
      assert s1.Peek(3) == 0x107;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x08fc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s10, gas - 1)
      else
        ExecuteFromCFGNode_s254(s10, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 117
    * Starting at 0x8f9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x102

    requires s0.stack[4] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x102;
      assert s1.Peek(5) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 255
    * Segment Id for this node is: 118
    * Starting at 0x8fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x102

    requires s0.stack[4] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      assert s1.Peek(4) == 0x107;
      var s2 := Push2(s1, 0x0905);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x08d1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s256(s5, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 113
    * Starting at 0x8d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x905

    requires s0.stack[5] == 0x102

    requires s0.stack[6] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x905;
      assert s1.Peek(5) == 0x102;
      assert s1.Peek(6) == 0x107;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x905;
      assert s11.Peek(8) == 0x102;
      assert s11.Peek(9) == 0x107;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x08e7);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s258(s14, gas - 1)
      else
        ExecuteFromCFGNode_s257(s14, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 114
    * Starting at 0x8e4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x905

    requires s0.stack[6] == 0x102

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x905;
      assert s1.Peek(7) == 0x102;
      assert s1.Peek(8) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 258
    * Segment Id for this node is: 115
    * Starting at 0x8e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x905

    requires s0.stack[6] == 0x102

    requires s0.stack[7] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x905;
      assert s1.Peek(6) == 0x102;
      assert s1.Peek(7) == 0x107;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s5, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 119
    * Starting at 0x905
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x905 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x102

    requires s0.stack[5] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x102;
      assert s1.Peek(5) == 0x107;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s7, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 26
    * Starting at 0x102
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x107;
      var s2 := Push2(s1, 0x0262);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s3, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 53
    * Starting at 0x262
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x262 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x107;
      var s2 := Push1(s1, 0x0a);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup3(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(4) == 0x107;
      var s12 := Push0(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x07);
      var s17 := Push1(s16, 0x20);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup2(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(5) == 0x107;
      var s22 := Dup1(s21);
      var s23 := SLoad(s22);
      var s24 := Push1(s23, 0xff);
      var s25 := Not(s24);
      var s26 := And(s25);
      var s27 := Push1(s26, 0xff);
      var s28 := Swap1(s27);
      var s29 := Swap5(s28);
      var s30 := And(s29);
      var s31 := IsZero(s30);
      assert s31.Peek(6) == 0x107;
      var s32 := IsZero(s31);
      var s33 := Swap4(s32);
      var s34 := Swap1(s33);
      var s35 := Swap4(s34);
      var s36 := Or(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := SStore(s38);
      var s40 := Push1(s39, 0x04);
      var s41 := SLoad(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s262(s41, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 54
    * Starting at 0x295
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(5) == 0x107;
      var s2 := Swap2(s1);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Eq(s10);
      assert s11.Peek(4) == 0x107;
      var s12 := Push2(s11, 0x02aa);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s13, gas - 1)
      else
        ExecuteFromCFGNode_s263(s13, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 55
    * Starting at 0x2a7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x107

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x107;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 264
    * Segment Id for this node is: 24
    * Starting at 0xf0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0 as nat
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
