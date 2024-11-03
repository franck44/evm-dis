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
      var s6 := Push2(s5, 0x003f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s40(s7, gas - 1)
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
      var s6 := Push4(s5, 0x969eba22);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x0043);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s30(s9, gas - 1)
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
      var s2 := Push4(s1, 0xbcce31b4);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0069);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s5, gas - 1)
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
      var s2 := Push4(s1, 0xc184f236);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00d7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s7(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x3f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
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
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 7
    * Segment Id for this node is: 15
    * Starting at 0xd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00ea);
      var s3 := Push2(s2, 0x00e5);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x033d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s8(s7, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 34
    * Starting at 0x33d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xe5

    requires s0.stack[3] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe5;
      assert s1.Peek(3) == 0xea;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034d);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s10, gas - 1)
      else
        ExecuteFromCFGNode_s9(s10, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 35
    * Starting at 0x34a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xe5

    requires s0.stack[4] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0xe5;
      assert s1.Peek(5) == 0xea;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 10
    * Segment Id for this node is: 36
    * Starting at 0x34d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xe5

    requires s0.stack[4] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe5;
      assert s1.Peek(4) == 0xea;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s7, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 16
    * Starting at 0xe5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xea;
      var s2 := Push2(s1, 0x01b2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s3, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 22
    * Starting at 0x1b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xea;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Swap1(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(3) == 0xea;
      var s12 := Keccak256(s11);
      var s13 := Dup1(s12);
      var s14 := SLoad(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0xa0);
      var s18 := Shl(s17);
      var s19 := Sub(s18);
      var s20 := And(s19);
      var s21 := Push2(s20, 0x0226);
      assert s21.Peek(0) == 0x226;
      assert s21.Peek(4) == 0xea;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s22, gas - 1)
      else
        ExecuteFromCFGNode_s13(s22, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 23
    * Starting at 0x1cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0xea;
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
      assert s11.Peek(5) == 0xea;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x22);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x46756c66696c6c6d656e74207265717565737420646f6573206e6f7420657869);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0xea;
      var s22 := MStore(s21);
      var s23 := Push2(s22, 0x1cdd);
      var s24 := Push1(s23, 0xf2);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s14(s31, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 24
    * Starting at 0x21d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xea;
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

  /** Node 15
    * Segment Id for this node is: 25
    * Starting at 0x226
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x226 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xea;
      var s2 := Push1(s1, 0x03);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0xff);
      var s7 := And(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x027b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s10, gas - 1)
      else
        ExecuteFromCFGNode_s16(s10, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 26
    * Starting at 0x234
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x234 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0xea;
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
      assert s11.Peek(5) == 0xea;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x46756c66696c6c6d656e7420616c726561647920636f6d706c65746564000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0xea;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x021d);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s26, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 27
    * Starting at 0x27b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xea;
      var s2 := Push1(s1, 0x02);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x02bc);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s7, gas - 1)
      else
        ExecuteFromCFGNode_s18(s7, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 28
    * Starting at 0x285
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x285 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0xea;
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
      assert s11.Peek(5) == 0xea;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 13, 0x24b73b30b634b210383937b7b3);
      var s19 := Push1(s18, 0x99);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(5) == 0xea;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x021d);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s28, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 29
    * Starting at 0x2bc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xea;
      var s2 := Push1(s1, 0x03);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := SLoad(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Swap1(s10);
      assert s11.Peek(5) == 0xea;
      var s12 := Dup2(s11);
      var s13 := Or(s12);
      var s14 := Swap1(s13);
      var s15 := Swap2(s14);
      var s16 := SStore(s15);
      var s17 := Dup2(s16);
      var s18 := SLoad(s17);
      var s19 := Swap1(s18);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0xea;
      var s22 := SLoad(s21);
      var s23 := Push1(s22, 0x40);
      var s24 := Dup1(s23);
      var s25 := MLoad(s24);
      var s26 := Swap2(s25);
      var s27 := Dup3(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Dup3(s29);
      var s31 := Add(s30);
      assert s31.Peek(6) == 0xea;
      var s32 := Dup6(s31);
      var s33 := Swap1(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x01);
      var s36 := Push1(s35, 0x01);
      var s37 := Push1(s36, 0xa0);
      var s38 := Shl(s37);
      var s39 := Sub(s38);
      var s40 := Swap1(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s20(s41, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 30
    * Starting at 0x2ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(5) == 0xea;
      var s2 := Swap2(s1);
      var s3 := Push32(s2, 0xb7d085c89a2330ef0d577d6f87329e4a20533a9bb8dc6b2e5d03658a1b17ddb3);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Swap2(s8);
      var s10 := Sub(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0xea;
      var s12 := Log2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s15, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 17
    * Starting at 0xea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
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

  /** Node 22
    * Segment Id for this node is: 11
    * Starting at 0x69
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00ab);
      var s3 := Push2(s2, 0x0077);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x033d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s7, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 34
    * Starting at 0x33d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x77

    requires s0.stack[3] == 0xab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x77;
      assert s1.Peek(3) == 0xab;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x034d);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s10, gas - 1)
      else
        ExecuteFromCFGNode_s24(s10, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 35
    * Starting at 0x34a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x77

    requires s0.stack[4] == 0xab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x77;
      assert s1.Peek(5) == 0xab;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 25
    * Segment Id for this node is: 36
    * Starting at 0x34d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x77

    requires s0.stack[4] == 0xab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x77;
      assert s1.Peek(4) == 0xab;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s7, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 12
    * Starting at 0x77
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xab;
      var s2 := Push0(s1);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Swap1(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xab;
      var s12 := Keccak256(s11);
      var s13 := Dup1(s12);
      var s14 := SLoad(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := SLoad(s17);
      var s19 := Push1(s18, 0x02);
      var s20 := Dup4(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0xab;
      var s22 := SLoad(s21);
      var s23 := Push1(s22, 0x03);
      var s24 := Swap1(s23);
      var s25 := Swap4(s24);
      var s26 := Add(s25);
      var s27 := SLoad(s26);
      var s28 := Push1(s27, 0x01);
      var s29 := Push1(s28, 0x01);
      var s30 := Push1(s29, 0xa0);
      var s31 := Shl(s30);
      assert s31.Peek(6) == 0xab;
      var s32 := Sub(s31);
      var s33 := Swap1(s32);
      var s34 := Swap3(s33);
      var s35 := And(s34);
      var s36 := Swap4(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := Swap2(s38);
      var s40 := Push1(s39, 0xff);
      var s41 := And(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s27(s41, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 13
    * Starting at 0xa9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0xab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(0) == 0xab;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s2, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 14
    * Starting at 0xab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Swap6(s10);
      var s12 := And(s11);
      var s13 := Dup6(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Swap4(s17);
      var s19 := Swap1(s18);
      var s20 := Swap4(s19);
      var s21 := MStore(s20);
      var s22 := Swap2(s21);
      var s23 := Dup4(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := IsZero(s25);
      var s27 := IsZero(s26);
      var s28 := Push1(s27, 0x60);
      var s29 := Dup3(s28);
      var s30 := Add(s29);
      var s31 := MStore(s30);
      var s32 := Push1(s31, 0x80);
      var s33 := Add(s32);
      var s34 := Push2(s33, 0x0060);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s35, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 10
    * Starting at 0x60
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60 as nat
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

  /** Node 30
    * Segment Id for this node is: 7
    * Starting at 0x43
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0056);
      var s3 := Push2(s2, 0x0051);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x031d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s7, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 31
    * Starting at 0x31d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x51

    requires s0.stack[3] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x51;
      assert s1.Peek(3) == 0x56;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x032e);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s11, gas - 1)
      else
        ExecuteFromCFGNode_s32(s11, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 32
    * Starting at 0x32b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x51

    requires s0.stack[5] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x51;
      assert s1.Peek(6) == 0x56;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 33
    * Segment Id for this node is: 33
    * Starting at 0x32e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x51

    requires s0.stack[5] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x51;
      assert s1.Peek(5) == 0x56;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Swap3(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := CallDataLoad(s10);
      assert s11.Peek(1) == 0x51;
      assert s11.Peek(4) == 0x56;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s14, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 8
    * Starting at 0x51
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x56;
      var s2 := Push2(s1, 0x00ec);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s3, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 18
    * Starting at 0xec
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x56;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 12, 0xffffffffffffffffffffffff);
      var s5 := Not(s4);
      var s6 := Caller(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Shl(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup3(s10);
      assert s11.Peek(6) == 0x56;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x34);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Dup4(s16);
      var s18 := Swap1(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x54);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0x56;
      var s22 := Add(s21);
      var s23 := Dup3(s22);
      var s24 := Swap1(s23);
      var s25 := MStore(s24);
      var s26 := TimeStamp(s25);
      var s27 := Push1(s26, 0x74);
      var s28 := Dup3(s27);
      var s29 := Add(s28);
      var s30 := MStore(s29);
      var s31 := Push0(s30);
      assert s31.Peek(4) == 0x56;
      var s32 := Swap1(s31);
      var s33 := Dup2(s32);
      var s34 := Swap1(s33);
      var s35 := Push1(s34, 0x94);
      var s36 := Add(s35);
      var s37 := Push1(s36, 0x40);
      var s38 := Dup1(s37);
      var s39 := MLoad(s38);
      var s40 := Push1(s39, 0x1f);
      var s41 := Not(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s36(s41, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 19
    * Starting at 0x12a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x56;
      var s2 := Dup5(s1);
      var s3 := Sub(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := MStore(s8);
      var s10 := Dup1(s9);
      var s11 := MLoad(s10);
      assert s11.Peek(8) == 0x56;
      var s12 := Push1(s11, 0x20);
      var s13 := Swap2(s12);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := Keccak256(s15);
      var s17 := Push0(s16);
      var s18 := Dup2(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Dup1(s20);
      assert s21.Peek(10) == 0x56;
      var s22 := Dup4(s21);
      var s23 := MStore(s22);
      var s24 := Dup4(s23);
      var s25 := Swap1(s24);
      var s26 := Keccak256(s25);
      var s27 := Dup1(s26);
      var s28 := SLoad(s27);
      var s29 := Push1(s28, 0x01);
      var s30 := Push1(s29, 0x01);
      var s31 := Push1(s30, 0xa0);
      assert s31.Peek(13) == 0x56;
      var s32 := Shl(s31);
      var s33 := Sub(s32);
      var s34 := Not(s33);
      var s35 := And(s34);
      var s36 := Caller(s35);
      var s37 := Swap1(s36);
      var s38 := Dup2(s37);
      var s39 := Or(s38);
      var s40 := Dup3(s39);
      var s41 := SStore(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s37(s41, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 20
    * Starting at 0x157
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(11) == 0x56;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup11(s3);
      var s5 := Swap1(s4);
      var s6 := SStore(s5);
      var s7 := Push1(s6, 0x02);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Dup10(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(12) == 0x56;
      var s12 := SStore(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := Dup1(s15);
      var s17 := SLoad(s16);
      var s18 := Push1(s17, 0xff);
      var s19 := Not(s18);
      var s20 := And(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(12) == 0x56;
      var s22 := SStore(s21);
      var s23 := Dup10(s22);
      var s24 := Dup7(s23);
      var s25 := MStore(s24);
      var s26 := Swap3(s25);
      var s27 := Dup6(s26);
      var s28 := Add(s27);
      var s29 := Dup3(s28);
      var s30 := Swap1(s29);
      var s31 := MStore(s30);
      assert s31.Peek(9) == 0x56;
      var s32 := Swap1(s31);
      var s33 := Swap5(s32);
      var s34 := Pop(s33);
      var s35 := Swap3(s34);
      var s36 := Swap1(s35);
      var s37 := Swap2(s36);
      var s38 := Push32(s37, 0x8f8414bf9a67d5f566d03655fd55f13d4028b856afcdd3a64d8803ba2aaca77b);
      var s39 := Swap2(s38);
      var s40 := Add(s39);
      var s41 := Push1(s40, 0x40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s38(s41, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 21
    * Starting at 0x1a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MLoad(s0);
      assert s1.Peek(9) == 0x56;
      var s2 := Dup1(s1);
      var s3 := Swap2(s2);
      var s4 := Sub(s3);
      var s5 := Swap1(s4);
      var s6 := Log2(s5);
      var s7 := Pop(s6);
      var s8 := Swap4(s7);
      var s9 := Swap3(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x56;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s13, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 9
    * Starting at 0x56
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x56 as nat
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
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s29(s8, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 6
    * Starting at 0x3f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f as nat
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
