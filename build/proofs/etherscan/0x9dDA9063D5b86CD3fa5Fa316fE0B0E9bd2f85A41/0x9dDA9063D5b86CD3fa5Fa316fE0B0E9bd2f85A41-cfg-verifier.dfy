include "../../../../src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module  {:disableNonlinearArithmetic} EVMProofObject {

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
      var s1 := Push1(s0, 0x80);
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x04);
      var s5 := CallDataSize(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x00c9);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s290(s8, gas - 1)
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
      var s1 := Push1(s0, 0x00);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shr(s3);
      var s5 := Dup1(s4);
      var s6 := Push4(s5, 0x6a42b8f8);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x0079);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s9, gas - 1)
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
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xc1a287e2);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0056);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s5, gas - 1)
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
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xc1a287e2);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0217);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s5, gas - 1)
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
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xe177246e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x022d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
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
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf2b06537);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x024d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s13(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x4a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf851a440);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x028d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x55
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0);
      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 8
    * Segment Id for this node is: 68
    * Starting at 0x28d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0299);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s6, gas - 1)
      else
        ExecuteFromCFGNode_s9(s6, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 69
    * Starting at 0x295
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 10
    * Segment Id for this node is: 70
    * Starting at 0x299
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x0143);
      var s6 := Swap1(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s10, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 33
    * Starting at 0x143
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x143

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x143;
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
      assert s11.Peek(1) == 0x143;
      var s12 := Push2(s11, 0x00f8);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s13, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 26
    * Starting at 0xf8
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x143

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x143;
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
    * Segment Id for this node is: 63
    * Starting at 0x24d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0259);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s6, gas - 1)
      else
        ExecuteFromCFGNode_s14(s6, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 64
    * Starting at 0x255
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x255 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 15
    * Segment Id for this node is: 65
    * Starting at 0x259
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x259 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x027d);
      var s4 := Push2(s3, 0x0268);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x119a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s8, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 164
    * Starting at 0x119a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x119a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x268

    requires s0.stack[3] == 0x27d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x268;
      assert s1.Peek(3) == 0x27d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x11ac);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s18(s10, gas - 1)
      else
        ExecuteFromCFGNode_s17(s10, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 165
    * Starting at 0x11a8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x268

    requires s0.stack[4] == 0x27d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x268;
      assert s1.Peek(5) == 0x27d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 18
    * Segment Id for this node is: 166
    * Starting at 0x11ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x268

    requires s0.stack[4] == 0x27d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x268;
      assert s1.Peek(4) == 0x27d;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s7, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 66
    * Starting at 0x268
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x268 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x27d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x27d;
      var s2 := Push1(s1, 0x03);
      var s3 := Push1(s2, 0x20);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Swap1(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x27d;
      var s12 := SLoad(s11);
      var s13 := Push1(s12, 0xff);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s16, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 67
    * Starting at 0x27d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x27d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x27d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x00f8);
      assert s11.Peek(0) == 0xf8;
      assert s11.Peek(2) == 0x27d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s12, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 26
    * Starting at 0xf8
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x27d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x27d;
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

  /** Node 22
    * Segment Id for this node is: 59
    * Starting at 0x22d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0239);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s6, gas - 1)
      else
        ExecuteFromCFGNode_s23(s6, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 60
    * Starting at 0x235
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x235 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 24
    * Segment Id for this node is: 61
    * Starting at 0x239
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x239 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00c9);
      var s4 := Push2(s3, 0x0248);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x119a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s8, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 164
    * Starting at 0x119a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x119a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x248

    requires s0.stack[3] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x248;
      assert s1.Peek(3) == 0xc9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x11ac);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s10, gas - 1)
      else
        ExecuteFromCFGNode_s26(s10, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 165
    * Starting at 0x11a8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x248

    requires s0.stack[4] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x248;
      assert s1.Peek(5) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 27
    * Segment Id for this node is: 166
    * Starting at 0x11ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x248

    requires s0.stack[4] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x248;
      assert s1.Peek(4) == 0xc9;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s7, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 62
    * Starting at 0x248
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x248 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      var s2 := Push2(s1, 0x0e14);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s3, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 124
    * Starting at 0xe14
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      var s2 := Caller(s1);
      var s3 := Address(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0e89);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s32(s6, gas - 1)
      else
        ExecuteFromCFGNode_s30(s6, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 125
    * Starting at 0xe1c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0xc9;
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
      assert s11.Peek(4) == 0xc9;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x31);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a73657444656c61793a2043616c6c206d75737420636f);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0xc9;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6d652066726f6d2054696d656c6f636b2e000000000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s31, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 73
    * Starting at 0x346
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc9;
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

  /** Node 32
    * Segment Id for this node is: 126
    * Starting at 0xe89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      var s2 := Push2(s1, 0x0e10);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0f01);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s7, gas - 1)
      else
        ExecuteFromCFGNode_s33(s7, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 127
    * Starting at 0xe94
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0xc9;
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
      assert s11.Peek(4) == 0xc9;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x34);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a73657444656c61793a2044656c6179206d7573742065);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0xc9;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x7863656564206d696e696d756d2064656c61792e000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s31, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 128
    * Starting at 0xf01
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf01 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      var s2 := Push3(s1, 0x278d00);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0f7a);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s7, gas - 1)
      else
        ExecuteFromCFGNode_s35(s7, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 129
    * Starting at 0xf0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0xc9;
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
      assert s11.Peek(4) == 0xc9;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x38);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a73657444656c61793a2044656c6179206d757374206e);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0xc9;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6f7420657863656564206d6178696d756d2064656c61792e0000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s31, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 130
    * Starting at 0xf7a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      var s2 := Push1(s1, 0x02);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup3(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Push32(s8, 0xed0229422af39d4d7d33f7a27d31d6f5cb20ec628293da58dd6e8a528ed466be);
      var s10 := Swap1(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(6) == 0xc9;
      var s12 := Swap1(s11);
      var s13 := Log3(s12);
      var s14 := Push1(s13, 0x02);
      var s15 := SStore(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s16, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 20
    * Starting at 0xc9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9 as nat
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

  /** Node 38
    * Segment Id for this node is: 56
    * Starting at 0x217
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x217 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0223);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s40(s6, gas - 1)
      else
        ExecuteFromCFGNode_s39(s6, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 57
    * Starting at 0x21f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 40
    * Segment Id for this node is: 58
    * Starting at 0x223
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x223 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push3(s2, 0x127500);
      var s4 := Push2(s3, 0x0188);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s5, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 38
    * Starting at 0x188
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x188 as nat
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
      var s9 := Push2(s8, 0x00f8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s10, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 26
    * Starting at 0xf8
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8 as nat
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

  /** Node 43
    * Segment Id for this node is: 8
    * Starting at 0x56
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x6a42b8f8);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x01d6);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s6, gas - 1)
      else
        ExecuteFromCFGNode_s44(s6, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 9
    * Starting at 0x62
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x7d645fab);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01ec);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s5, gas - 1)
      else
        ExecuteFromCFGNode_s45(s5, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 10
    * Starting at 0x6d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xb1b43ae5);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0202);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s5, gas - 1)
      else
        ExecuteFromCFGNode_s46(s5, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 11
    * Starting at 0x78
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0);
      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 47
    * Segment Id for this node is: 53
    * Starting at 0x202
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x202 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x020e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s6, gas - 1)
      else
        ExecuteFromCFGNode_s48(s6, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 54
    * Starting at 0x20a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 49
    * Segment Id for this node is: 55
    * Starting at 0x20e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0e10);
      var s4 := Push2(s3, 0x0188);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s5, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 50
    * Starting at 0x1ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x01f8);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s6, gas - 1)
      else
        ExecuteFromCFGNode_s51(s6, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 51
    * Starting at 0x1f4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 52
    * Segment Id for this node is: 52
    * Starting at 0x1f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push3(s2, 0x278d00);
      var s4 := Push2(s3, 0x0188);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s5, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 47
    * Starting at 0x1d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x01e2);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s6, gas - 1)
      else
        ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 48
    * Starting at 0x1de
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 55
    * Segment Id for this node is: 49
    * Starting at 0x1e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0188);
      var s4 := Push1(s3, 0x02);
      var s5 := SLoad(s4);
      var s6 := Dup2(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s7, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 38
    * Starting at 0x188
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x188 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x188;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x00f8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s10, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 26
    * Starting at 0xf8
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x188;
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

  /** Node 58
    * Segment Id for this node is: 12
    * Starting at 0x79
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x3a66f901);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00a7);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s6, gas - 1)
      else
        ExecuteFromCFGNode_s59(s6, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 13
    * Starting at 0x85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x3a66f901);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0168);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s134(s5, gas - 1)
      else
        ExecuteFromCFGNode_s60(s5, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 14
    * Starting at 0x90
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x4dd18bf5);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0196);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s5, gas - 1)
      else
        ExecuteFromCFGNode_s61(s5, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 15
    * Starting at 0x9b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x591fcdfe);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01b6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s5, gas - 1)
      else
        ExecuteFromCFGNode_s62(s5, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 16
    * Starting at 0xa6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0);
      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 63
    * Segment Id for this node is: 43
    * Starting at 0x1b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x01c2);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s6, gas - 1)
      else
        ExecuteFromCFGNode_s64(s6, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 44
    * Starting at 0x1be
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 65
    * Segment Id for this node is: 45
    * Starting at 0x1c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00c9);
      var s4 := Push2(s3, 0x01d1);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x1070);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s8, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 144
    * Starting at 0x1070
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1d1

    requires s0.stack[3] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1d1;
      assert s1.Peek(3) == 0xc9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Push1(s8, 0xa0);
      var s10 := Dup9(s9);
      var s11 := Dup11(s10);
      assert s11.Peek(12) == 0x1d1;
      assert s11.Peek(13) == 0xc9;
      var s12 := Sub(s11);
      var s13 := SLt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x108b);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s16, gas - 1)
      else
        ExecuteFromCFGNode_s67(s16, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 145
    * Starting at 0x1087
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1087 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x1d1

    requires s0.stack[10] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(10) == 0x1d1;
      assert s1.Peek(11) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 68
    * Segment Id for this node is: 146
    * Starting at 0x108b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x1d1

    requires s0.stack[10] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x1d1;
      assert s1.Peek(10) == 0xc9;
      var s2 := Push2(s1, 0x1094);
      var s3 := Dup9(s2);
      var s4 := Push2(s3, 0x0ffe);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s5, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 134
    * Starting at 0xffe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x1094

    requires s0.stack[11] == 0x1d1

    requires s0.stack[12] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1094;
      assert s1.Peek(11) == 0x1d1;
      assert s1.Peek(12) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x1022);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s10, gas - 1)
      else
        ExecuteFromCFGNode_s70(s10, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 135
    * Starting at 0x101e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x1094

    requires s0.stack[12] == 0x1d1

    requires s0.stack[13] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x1094;
      assert s1.Peek(13) == 0x1d1;
      assert s1.Peek(14) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 71
    * Segment Id for this node is: 136
    * Starting at 0x1022
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1022 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x1094

    requires s0.stack[12] == 0x1d1

    requires s0.stack[13] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1094;
      assert s1.Peek(12) == 0x1d1;
      assert s1.Peek(13) == 0xc9;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s5, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 147
    * Starting at 0x1094
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x1d1

    requires s0.stack[11] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x1d1;
      assert s1.Peek(11) == 0xc9;
      var s2 := Swap7(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup9(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Swap6(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x1d1;
      assert s11.Peek(12) == 0xc9;
      var s12 := Add(s11);
      var s13 := CallDataLoad(s12);
      var s14 := Push8(s13, 0xffffffffffffffff);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Gt(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x10b8);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s20, gas - 1)
      else
        ExecuteFromCFGNode_s73(s20, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 148
    * Starting at 0x10b4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x1d1

    requires s0.stack[12] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x1d1;
      assert s1.Peek(13) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 74
    * Segment Id for this node is: 149
    * Starting at 0x10b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x1d1

    requires s0.stack[12] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x1d1;
      assert s1.Peek(12) == 0xc9;
      var s2 := Push2(s1, 0x10c4);
      var s3 := Dup12(s2);
      var s4 := Dup4(s3);
      var s5 := Dup13(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x1027);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s8, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 137
    * Starting at 0x1027
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1027 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x10c4

    requires s0.stack[14] == 0x1d1

    requires s0.stack[15] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10c4;
      assert s1.Peek(14) == 0x1d1;
      assert s1.Peek(15) == 0xc9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x1039);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s10, gas - 1)
      else
        ExecuteFromCFGNode_s76(s10, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 138
    * Starting at 0x1035
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x1d1

    requires s0.stack[17] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10c4;
      assert s1.Peek(17) == 0x1d1;
      assert s1.Peek(18) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 77
    * Segment Id for this node is: 139
    * Starting at 0x1039
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1039 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x1d1

    requires s0.stack[17] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10c4;
      assert s1.Peek(16) == 0x1d1;
      assert s1.Peek(17) == 0xc9;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Push8(s4, 0xffffffffffffffff);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1051);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s10, gas - 1)
      else
        ExecuteFromCFGNode_s78(s10, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 140
    * Starting at 0x104d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x1d1

    requires s0.stack[17] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10c4;
      assert s1.Peek(17) == 0x1d1;
      assert s1.Peek(18) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 79
    * Segment Id for this node is: 141
    * Starting at 0x1051
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x1d1

    requires s0.stack[17] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10c4;
      assert s1.Peek(16) == 0x1d1;
      assert s1.Peek(17) == 0xc9;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Dup6(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x10c4;
      assert s11.Peek(19) == 0x1d1;
      assert s11.Peek(20) == 0xc9;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x1069);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s16, gas - 1)
      else
        ExecuteFromCFGNode_s80(s16, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 142
    * Starting at 0x1065
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1065 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x1d1

    requires s0.stack[17] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10c4;
      assert s1.Peek(17) == 0x1d1;
      assert s1.Peek(18) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 81
    * Segment Id for this node is: 143
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x1d1

    requires s0.stack[17] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10c4;
      assert s1.Peek(16) == 0x1d1;
      assert s1.Peek(17) == 0xc9;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s7, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 150
    * Starting at 0x10c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x1d1

    requires s0.stack[14] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x1d1;
      assert s1.Peek(14) == 0xc9;
      var s2 := Swap1(s1);
      var s3 := Swap(s2, 8);
      var s4 := Pop(s3);
      var s5 := Swap6(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Dup11(s7);
      var s9 := Add(s8);
      var s10 := CallDataLoad(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(12) == 0x1d1;
      assert s11.Peek(13) == 0xc9;
      var s12 := Pop(s11);
      var s13 := Dup1(s12);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x10dd);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s18, gas - 1)
      else
        ExecuteFromCFGNode_s83(s18, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 151
    * Starting at 0x10d9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x1d1

    requires s0.stack[12] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x1d1;
      assert s1.Peek(13) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 84
    * Segment Id for this node is: 152
    * Starting at 0x10dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x1d1

    requires s0.stack[12] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x1d1;
      assert s1.Peek(12) == 0xc9;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x10ea);
      var s4 := Dup11(s3);
      var s5 := Dup3(s4);
      var s6 := Dup12(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x1027);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s9, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 137
    * Starting at 0x1027
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1027 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x10ea

    requires s0.stack[13] == 0x1d1

    requires s0.stack[14] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ea;
      assert s1.Peek(13) == 0x1d1;
      assert s1.Peek(14) == 0xc9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x1039);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s10, gas - 1)
      else
        ExecuteFromCFGNode_s86(s10, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 138
    * Starting at 0x1035
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x1d1

    requires s0.stack[16] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10ea;
      assert s1.Peek(16) == 0x1d1;
      assert s1.Peek(17) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 87
    * Segment Id for this node is: 139
    * Starting at 0x1039
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1039 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x1d1

    requires s0.stack[16] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10ea;
      assert s1.Peek(15) == 0x1d1;
      assert s1.Peek(16) == 0xc9;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Push8(s4, 0xffffffffffffffff);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1051);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s10, gas - 1)
      else
        ExecuteFromCFGNode_s88(s10, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 140
    * Starting at 0x104d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x1d1

    requires s0.stack[16] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10ea;
      assert s1.Peek(16) == 0x1d1;
      assert s1.Peek(17) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 89
    * Segment Id for this node is: 141
    * Starting at 0x1051
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x1d1

    requires s0.stack[16] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10ea;
      assert s1.Peek(15) == 0x1d1;
      assert s1.Peek(16) == 0xc9;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Dup6(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x10ea;
      assert s11.Peek(18) == 0x1d1;
      assert s11.Peek(19) == 0xc9;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x1069);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s91(s16, gas - 1)
      else
        ExecuteFromCFGNode_s90(s16, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 142
    * Starting at 0x1065
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1065 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x1d1

    requires s0.stack[16] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10ea;
      assert s1.Peek(16) == 0x1d1;
      assert s1.Peek(17) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 91
    * Segment Id for this node is: 143
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x1d1

    requires s0.stack[16] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10ea;
      assert s1.Peek(15) == 0x1d1;
      assert s1.Peek(16) == 0xc9;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s7, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 153
    * Starting at 0x10ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[12] == 0x1d1

    requires s0.stack[13] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x1d1;
      assert s1.Peek(13) == 0xc9;
      var s2 := Swap(s1, 9);
      var s3 := Swap(s2, 12);
      var s4 := Swap(s3, 8);
      var s5 := Swap(s4, 11);
      var s6 := Pop(s5);
      var s7 := Swap6(s6);
      var s8 := Swap(s7, 9);
      var s9 := Swap5(s8);
      var s10 := Swap(s9, 8);
      var s11 := Swap6(s10);
      assert s11.Peek(7) == 0x1d1;
      assert s11.Peek(12) == 0xc9;
      var s12 := Swap7(s11);
      var s13 := Push1(s12, 0x80);
      var s14 := Swap1(s13);
      var s15 := Swap6(s14);
      var s16 := Add(s15);
      var s17 := CallDataLoad(s16);
      var s18 := Swap5(s17);
      var s19 := Swap4(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(2) == 0x1d1;
      assert s21.Peek(10) == 0xc9;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s24, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 46
    * Starting at 0x1d1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xc9;
      var s2 := Push2(s1, 0x0c13);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s3, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 116
    * Starting at 0xc13
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xc9;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Caller(s5);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x0ca0);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s97(s9, gas - 1)
      else
        ExecuteFromCFGNode_s95(s9, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 117
    * Starting at 0xc33
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(8) == 0xc9;
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
      assert s11.Peek(10) == 0xc9;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x37);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a63616e63656c5472616e73616374696f6e3a2043616c);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(10) == 0xc9;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6c206d75737420636f6d652066726f6d2061646d696e2e000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s31, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 73
    * Starting at 0x346
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xc9;
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

  /** Node 97
    * Segment Id for this node is: 118
    * Starting at 0xca0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xc9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup8(s2);
      var s4 := Dup8(s3);
      var s5 := Dup8(s4);
      var s6 := Dup8(s5);
      var s7 := Dup8(s6);
      var s8 := Dup8(s7);
      var s9 := Dup8(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(16) == 0xc9;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Push2(s13, 0x0cbf);
      var s15 := Swap(s14, 8);
      var s16 := Swap7(s15);
      var s17 := Swap6(s16);
      var s18 := Swap5(s17);
      var s19 := Swap4(s18);
      var s20 := Swap3(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(8) == 0xcbf;
      assert s21.Peek(17) == 0xc9;
      var s22 := Swap1(s21);
      var s23 := Push2(s22, 0x11fc);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s24, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 168
    * Starting at 0x11fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0xcbf

    requires s0.stack[17] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xcbf;
      assert s1.Peek(17) == 0xc9;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup9(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Dup7(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(8) == 0xcbf;
      assert s11.Peek(17) == 0xc9;
      var s12 := Push1(s11, 0xa0);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Push2(s17, 0x1232);
      var s19 := Push1(s18, 0xa0);
      var s20 := Dup4(s19);
      var s21 := Add(s20);
      assert s21.Peek(1) == 0x1232;
      assert s21.Peek(11) == 0xcbf;
      assert s21.Peek(20) == 0xc9;
      var s22 := Dup8(s21);
      var s23 := Dup10(s22);
      var s24 := Push2(s23, 0x11b3);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s25, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0x1232

    requires s0.stack[13] == 0xcbf

    requires s0.stack[22] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1232;
      assert s1.Peek(13) == 0xcbf;
      assert s1.Peek(22) == 0xc9;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x1232;
      assert s11.Peek(12) == 0xcbf;
      assert s11.Peek(21) == 0xc9;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x1232;
      assert s21.Peek(15) == 0xcbf;
      assert s21.Peek(24) == 0xc9;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x1232;
      assert s31.Peek(13) == 0xcbf;
      assert s31.Peek(22) == 0xc9;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s35, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 169
    * Starting at 0x1232
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1232 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0xcbf

    requires s0.stack[19] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xcbf;
      assert s1.Peek(19) == 0xc9;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push2(s8, 0x1245);
      var s10 := Dup2(s9);
      var s11 := Dup7(s10);
      assert s11.Peek(2) == 0x1245;
      assert s11.Peek(13) == 0xcbf;
      assert s11.Peek(22) == 0xc9;
      var s12 := Dup9(s11);
      var s13 := Push2(s12, 0x11b3);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s14, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x1245

    requires s0.stack[14] == 0xcbf

    requires s0.stack[23] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1245;
      assert s1.Peek(14) == 0xcbf;
      assert s1.Peek(23) == 0xc9;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x1245;
      assert s11.Peek(13) == 0xcbf;
      assert s11.Peek(22) == 0xc9;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x1245;
      assert s21.Peek(16) == 0xcbf;
      assert s21.Peek(25) == 0xc9;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x1245;
      assert s31.Peek(14) == 0xcbf;
      assert s31.Peek(23) == 0xc9;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s35, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 170
    * Starting at 0x1245
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1245 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0xcbf

    requires s0.stack[20] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0xcbf;
      assert s1.Peek(20) == 0xc9;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup3(s4);
      var s6 := Push1(s5, 0x80);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Swap(s9, 9);
      var s11 := Swap(s10, 8);
      assert s11.Peek(8) == 0xcbf;
      assert s11.Peek(18) == 0xc9;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Pop(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s20, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 119
    * Starting at 0xcbf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xc9;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(11) == 0xc9;
      var s12 := Swap2(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Dup2(s14);
      var s16 := MLoad(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Swap3(s17);
      var s19 := Dup4(s18);
      var s20 := Add(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(11) == 0xc9;
      var s22 := Push1(s21, 0x00);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x03);
      var s27 := Swap1(s26);
      var s28 := Swap4(s27);
      var s29 := MStore(s28);
      var s30 := Swap2(s29);
      var s31 := Keccak256(s30);
      assert s31.Peek(10) == 0xc9;
      var s32 := SLoad(s31);
      var s33 := Swap1(s32);
      var s34 := Swap2(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0xff);
      var s37 := And(s36);
      var s38 := Push2(s37, 0x0d7a);
      var s39 := JumpI(s38);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s38.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s39, gas - 1)
      else
        ExecuteFromCFGNode_s104(s39, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 120
    * Starting at 0xd0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0xc9;
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
      assert s11.Peek(11) == 0xc9;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x3b);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a63616e63656c5472616e73616374696f6e3a20747261);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(11) == 0xc9;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6e73616374696f6e206973206e6f7420717565756564207965742e0000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s31, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 73
    * Starting at 0x346
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xc9;
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

  /** Node 106
    * Segment Id for this node is: 121
    * Starting at 0xd7a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xc9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x03);
      var s7 := Push1(s6, 0x20);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(11) == 0xc9;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Dup1(s13);
      var s15 := SLoad(s14);
      var s16 := Push32(s15, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00);
      var s17 := And(s16);
      var s18 := Swap1(s17);
      var s19 := SStore(s18);
      var s20 := MLoad(s19);
      var s21 := Push20(s20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s21.Peek(10) == 0xc9;
      var s22 := Dup10(s21);
      var s23 := And(s22);
      var s24 := Swap1(s23);
      var s25 := Dup3(s24);
      var s26 := Swap1(s25);
      var s27 := Push32(s26, 0x2fffc091a501fd91bfbff27141450d3acb40fb8e6d8382b243ec7a812a3aaf87);
      var s28 := Swap1(s27);
      var s29 := Push2(s28, 0x0e02);
      var s30 := Swap1(s29);
      var s31 := Dup12(s30);
      assert s31.Peek(2) == 0xe02;
      assert s31.Peek(14) == 0xc9;
      var s32 := Swap1(s31);
      var s33 := Dup12(s32);
      var s34 := Swap1(s33);
      var s35 := Dup12(s34);
      var s36 := Swap1(s35);
      var s37 := Dup12(s36);
      var s38 := Swap1(s37);
      var s39 := Dup12(s38);
      var s40 := Swap1(s39);
      var s41 := Dup12(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s107(s41, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 122
    * Starting at 0xdfd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xe02

    requires s0.stack[19] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(7) == 0xe02;
      assert s1.Peek(19) == 0xc9;
      var s2 := Push2(s1, 0x1302);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s3, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 178
    * Starting at 0x1302
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1302 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xe02

    requires s0.stack[19] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xe02;
      assert s1.Peek(19) == 0xc9;
      var s2 := Dup7(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x80);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push2(s10, 0x131c);
      assert s11.Peek(0) == 0x131c;
      assert s11.Peek(9) == 0xe02;
      assert s11.Peek(21) == 0xc9;
      var s12 := Push1(s11, 0x80);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Dup8(s14);
      var s16 := Dup10(s15);
      var s17 := Push2(s16, 0x11b3);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s18, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x131c

    requires s0.stack[12] == 0xe02

    requires s0.stack[24] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x131c;
      assert s1.Peek(12) == 0xe02;
      assert s1.Peek(24) == 0xc9;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x131c;
      assert s11.Peek(11) == 0xe02;
      assert s11.Peek(23) == 0xc9;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x131c;
      assert s21.Peek(14) == 0xe02;
      assert s21.Peek(26) == 0xc9;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x131c;
      assert s31.Peek(12) == 0xe02;
      assert s31.Peek(24) == 0xc9;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s35, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 179
    * Starting at 0x131c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0xe02

    requires s0.stack[21] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xe02;
      assert s1.Peek(21) == 0xc9;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push2(s8, 0x132f);
      var s10 := Dup2(s9);
      var s11 := Dup7(s10);
      assert s11.Peek(2) == 0x132f;
      assert s11.Peek(12) == 0xe02;
      assert s11.Peek(24) == 0xc9;
      var s12 := Dup9(s11);
      var s13 := Push2(s12, 0x11b3);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s14, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0x132f

    requires s0.stack[13] == 0xe02

    requires s0.stack[25] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x132f;
      assert s1.Peek(13) == 0xe02;
      assert s1.Peek(25) == 0xc9;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x132f;
      assert s11.Peek(12) == 0xe02;
      assert s11.Peek(24) == 0xc9;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x132f;
      assert s21.Peek(15) == 0xe02;
      assert s21.Peek(27) == 0xc9;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x132f;
      assert s31.Peek(13) == 0xe02;
      assert s31.Peek(25) == 0xc9;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s35, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 180
    * Starting at 0x132f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -10
    * Net Capacity Effect: +10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[10] == 0xe02

    requires s0.stack[22] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xe02;
      assert s1.Peek(22) == 0xc9;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup3(s4);
      var s6 := Push1(s5, 0x60);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Swap(s9, 8);
      var s11 := Swap7(s10);
      assert s11.Peek(7) == 0xe02;
      assert s11.Peek(20) == 0xc9;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s19, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 123
    * Starting at 0xe02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -13
    * Net Capacity Effect: +13
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0xc9;
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
      assert s11.Peek(5) == 0xc9;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s17, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 39
    * Starting at 0x196
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x196 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x01a2);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s116(s6, gas - 1)
      else
        ExecuteFromCFGNode_s115(s6, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 40
    * Starting at 0x19e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 116
    * Segment Id for this node is: 41
    * Starting at 0x1a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00c9);
      var s4 := Push2(s3, 0x01b1);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x1178);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s8, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 160
    * Starting at 0x1178
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1178 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1b1

    requires s0.stack[3] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b1;
      assert s1.Peek(3) == 0xc9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x118a);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s119(s10, gas - 1)
      else
        ExecuteFromCFGNode_s118(s10, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 161
    * Starting at 0x1186
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1186 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1b1

    requires s0.stack[4] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1b1;
      assert s1.Peek(5) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 119
    * Segment Id for this node is: 162
    * Starting at 0x118a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1b1

    requires s0.stack[4] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1b1;
      assert s1.Peek(4) == 0xc9;
      var s2 := Push2(s1, 0x1193);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0ffe);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s5, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 134
    * Starting at 0xffe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x1193

    requires s0.stack[5] == 0x1b1

    requires s0.stack[6] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1193;
      assert s1.Peek(5) == 0x1b1;
      assert s1.Peek(6) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x1022);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s122(s10, gas - 1)
      else
        ExecuteFromCFGNode_s121(s10, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 135
    * Starting at 0x101e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x1193

    requires s0.stack[6] == 0x1b1

    requires s0.stack[7] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x1193;
      assert s1.Peek(7) == 0x1b1;
      assert s1.Peek(8) == 0xc9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 122
    * Segment Id for this node is: 136
    * Starting at 0x1022
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1022 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x1193

    requires s0.stack[6] == 0x1b1

    requires s0.stack[7] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1193;
      assert s1.Peek(6) == 0x1b1;
      assert s1.Peek(7) == 0xc9;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s5, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 163
    * Starting at 0x1193
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1193 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1b1

    requires s0.stack[5] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1b1;
      assert s1.Peek(5) == 0xc9;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s7, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 42
    * Starting at 0x1b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      var s2 := Push2(s1, 0x0b04);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s3, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 110
    * Starting at 0xb04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      var s2 := Caller(s1);
      var s3 := Address(s2);
      var s4 := Eq(s3);
      var s5 := Dup1(s4);
      var s6 := Push2(s5, 0x0b29);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s7, gas - 1)
      else
        ExecuteFromCFGNode_s126(s7, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 111
    * Starting at 0xb0d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0xc9;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Caller(s5);
      var s7 := Eq(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s127(s7, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 112
    * Starting at 0xb29
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb29 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc9;
      var s2 := Push2(s1, 0x0b9b);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s129(s3, gas - 1)
      else
        ExecuteFromCFGNode_s128(s3, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 113
    * Starting at 0xb2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0xc9;
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
      assert s11.Peek(4) == 0xc9;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x38);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a73657450656e64696e6741646d696e3a2043616c6c20);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0xc9;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6d75737420636f6d652066726f6d2054696d656c6f636b2e0000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s31, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 114
    * Starting at 0xb9b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      var s2 := Push2(s1, 0x0ba4);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fae);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s5, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 131
    * Starting at 0xfae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0xba4

    requires s0.stack[3] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xba4;
      assert s1.Peek(3) == 0xc9;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x0ffb);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s6, gas - 1)
      else
        ExecuteFromCFGNode_s131(s6, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 132
    * Starting at 0xfca
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0xba4

    requires s0.stack[3] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0xba4;
      assert s1.Peek(4) == 0xc9;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x8579befe00000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MLoad(s8);
      var s10 := Dup1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(4) == 0xba4;
      assert s11.Peek(6) == 0xc9;
      var s12 := Sub(s11);
      var s13 := Swap1(s12);
      var s14 := Revert(s13);
      // Segment is terminal (Revert, Stop or Return)
      s14
  }

  /** Node 132
    * Segment Id for this node is: 133
    * Starting at 0xffb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0xba4

    requires s0.stack[3] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xba4;
      assert s1.Peek(3) == 0xc9;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s3, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 115
    * Starting at 0xba4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000);
      var s6 := And(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := Dup4(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0xc9;
      var s12 := Or(s11);
      var s13 := Swap1(s12);
      var s14 := Swap2(s13);
      var s15 := SStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := MLoad(s16);
      var s18 := Push32(s17, 0x69d78e38a01985fbb1462961809b4b2d65531bc93b2b94037f3334b82ca4a756);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0x00);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0xc9;
      var s22 := Log2(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s24, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 34
    * Starting at 0x168
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x168 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0174);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s6, gas - 1)
      else
        ExecuteFromCFGNode_s135(s6, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 35
    * Starting at 0x170
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x170 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 136
    * Segment Id for this node is: 36
    * Starting at 0x174
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x174 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0188);
      var s4 := Push2(s3, 0x0183);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x1070);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s8, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 144
    * Starting at 0x1070
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x183

    requires s0.stack[3] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x183;
      assert s1.Peek(3) == 0x188;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Push1(s8, 0xa0);
      var s10 := Dup9(s9);
      var s11 := Dup11(s10);
      assert s11.Peek(12) == 0x183;
      assert s11.Peek(13) == 0x188;
      var s12 := Sub(s11);
      var s13 := SLt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x108b);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s16, gas - 1)
      else
        ExecuteFromCFGNode_s138(s16, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 145
    * Starting at 0x1087
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1087 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x183

    requires s0.stack[10] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(10) == 0x183;
      assert s1.Peek(11) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 139
    * Segment Id for this node is: 146
    * Starting at 0x108b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x183

    requires s0.stack[10] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x183;
      assert s1.Peek(10) == 0x188;
      var s2 := Push2(s1, 0x1094);
      var s3 := Dup9(s2);
      var s4 := Push2(s3, 0x0ffe);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s5, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 134
    * Starting at 0xffe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x1094

    requires s0.stack[11] == 0x183

    requires s0.stack[12] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1094;
      assert s1.Peek(11) == 0x183;
      assert s1.Peek(12) == 0x188;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x1022);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s142(s10, gas - 1)
      else
        ExecuteFromCFGNode_s141(s10, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 135
    * Starting at 0x101e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x1094

    requires s0.stack[12] == 0x183

    requires s0.stack[13] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x1094;
      assert s1.Peek(13) == 0x183;
      assert s1.Peek(14) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 142
    * Segment Id for this node is: 136
    * Starting at 0x1022
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1022 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x1094

    requires s0.stack[12] == 0x183

    requires s0.stack[13] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1094;
      assert s1.Peek(12) == 0x183;
      assert s1.Peek(13) == 0x188;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s5, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 147
    * Starting at 0x1094
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x183

    requires s0.stack[11] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x183;
      assert s1.Peek(11) == 0x188;
      var s2 := Swap7(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup9(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Swap6(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x183;
      assert s11.Peek(12) == 0x188;
      var s12 := Add(s11);
      var s13 := CallDataLoad(s12);
      var s14 := Push8(s13, 0xffffffffffffffff);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Gt(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x10b8);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s20, gas - 1)
      else
        ExecuteFromCFGNode_s144(s20, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 148
    * Starting at 0x10b4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x183

    requires s0.stack[12] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x183;
      assert s1.Peek(13) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 145
    * Segment Id for this node is: 149
    * Starting at 0x10b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x183

    requires s0.stack[12] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x183;
      assert s1.Peek(12) == 0x188;
      var s2 := Push2(s1, 0x10c4);
      var s3 := Dup12(s2);
      var s4 := Dup4(s3);
      var s5 := Dup13(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x1027);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s8, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 137
    * Starting at 0x1027
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1027 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x10c4

    requires s0.stack[14] == 0x183

    requires s0.stack[15] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10c4;
      assert s1.Peek(14) == 0x183;
      assert s1.Peek(15) == 0x188;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x1039);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s10, gas - 1)
      else
        ExecuteFromCFGNode_s147(s10, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 138
    * Starting at 0x1035
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x183

    requires s0.stack[17] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10c4;
      assert s1.Peek(17) == 0x183;
      assert s1.Peek(18) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 148
    * Segment Id for this node is: 139
    * Starting at 0x1039
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1039 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x183

    requires s0.stack[17] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10c4;
      assert s1.Peek(16) == 0x183;
      assert s1.Peek(17) == 0x188;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Push8(s4, 0xffffffffffffffff);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1051);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s150(s10, gas - 1)
      else
        ExecuteFromCFGNode_s149(s10, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 140
    * Starting at 0x104d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x183

    requires s0.stack[17] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10c4;
      assert s1.Peek(17) == 0x183;
      assert s1.Peek(18) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 150
    * Segment Id for this node is: 141
    * Starting at 0x1051
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x183

    requires s0.stack[17] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10c4;
      assert s1.Peek(16) == 0x183;
      assert s1.Peek(17) == 0x188;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Dup6(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x10c4;
      assert s11.Peek(19) == 0x183;
      assert s11.Peek(20) == 0x188;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x1069);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s16, gas - 1)
      else
        ExecuteFromCFGNode_s151(s16, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 142
    * Starting at 0x1065
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1065 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x183

    requires s0.stack[17] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10c4;
      assert s1.Peek(17) == 0x183;
      assert s1.Peek(18) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 152
    * Segment Id for this node is: 143
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0x183

    requires s0.stack[17] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10c4;
      assert s1.Peek(16) == 0x183;
      assert s1.Peek(17) == 0x188;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s7, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 150
    * Starting at 0x10c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0x183

    requires s0.stack[14] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x183;
      assert s1.Peek(14) == 0x188;
      var s2 := Swap1(s1);
      var s3 := Swap(s2, 8);
      var s4 := Pop(s3);
      var s5 := Swap6(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Dup11(s7);
      var s9 := Add(s8);
      var s10 := CallDataLoad(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(12) == 0x183;
      assert s11.Peek(13) == 0x188;
      var s12 := Pop(s11);
      var s13 := Dup1(s12);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x10dd);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s155(s18, gas - 1)
      else
        ExecuteFromCFGNode_s154(s18, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 151
    * Starting at 0x10d9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x183

    requires s0.stack[12] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x183;
      assert s1.Peek(13) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 155
    * Segment Id for this node is: 152
    * Starting at 0x10dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0x183

    requires s0.stack[12] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x183;
      assert s1.Peek(12) == 0x188;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x10ea);
      var s4 := Dup11(s3);
      var s5 := Dup3(s4);
      var s6 := Dup12(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x1027);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s9, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 137
    * Starting at 0x1027
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1027 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x10ea

    requires s0.stack[13] == 0x183

    requires s0.stack[14] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ea;
      assert s1.Peek(13) == 0x183;
      assert s1.Peek(14) == 0x188;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x1039);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s158(s10, gas - 1)
      else
        ExecuteFromCFGNode_s157(s10, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 138
    * Starting at 0x1035
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x183

    requires s0.stack[16] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10ea;
      assert s1.Peek(16) == 0x183;
      assert s1.Peek(17) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 158
    * Segment Id for this node is: 139
    * Starting at 0x1039
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1039 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x183

    requires s0.stack[16] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10ea;
      assert s1.Peek(15) == 0x183;
      assert s1.Peek(16) == 0x188;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Push8(s4, 0xffffffffffffffff);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1051);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s160(s10, gas - 1)
      else
        ExecuteFromCFGNode_s159(s10, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 140
    * Starting at 0x104d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x183

    requires s0.stack[16] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10ea;
      assert s1.Peek(16) == 0x183;
      assert s1.Peek(17) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 160
    * Segment Id for this node is: 141
    * Starting at 0x1051
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x183

    requires s0.stack[16] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10ea;
      assert s1.Peek(15) == 0x183;
      assert s1.Peek(16) == 0x188;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Dup6(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x10ea;
      assert s11.Peek(18) == 0x183;
      assert s11.Peek(19) == 0x188;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x1069);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s162(s16, gas - 1)
      else
        ExecuteFromCFGNode_s161(s16, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 142
    * Starting at 0x1065
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1065 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x183

    requires s0.stack[16] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10ea;
      assert s1.Peek(16) == 0x183;
      assert s1.Peek(17) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 162
    * Segment Id for this node is: 143
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0x183

    requires s0.stack[16] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10ea;
      assert s1.Peek(15) == 0x183;
      assert s1.Peek(16) == 0x188;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s7, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 153
    * Starting at 0x10ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[12] == 0x183

    requires s0.stack[13] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x183;
      assert s1.Peek(13) == 0x188;
      var s2 := Swap(s1, 9);
      var s3 := Swap(s2, 12);
      var s4 := Swap(s3, 8);
      var s5 := Swap(s4, 11);
      var s6 := Pop(s5);
      var s7 := Swap6(s6);
      var s8 := Swap(s7, 9);
      var s9 := Swap5(s8);
      var s10 := Swap(s9, 8);
      var s11 := Swap6(s10);
      assert s11.Peek(7) == 0x183;
      assert s11.Peek(12) == 0x188;
      var s12 := Swap7(s11);
      var s13 := Push1(s12, 0x80);
      var s14 := Swap1(s13);
      var s15 := Swap6(s14);
      var s16 := Add(s15);
      var s17 := CallDataLoad(s16);
      var s18 := Swap5(s17);
      var s19 := Swap4(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(2) == 0x183;
      assert s21.Peek(10) == 0x188;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s24, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 37
    * Starting at 0x183
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x183 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x188;
      var s2 := Push2(s1, 0x0854);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s3, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 99
    * Starting at 0x854
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x854 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x188;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Caller(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x08e2);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s168(s10, gas - 1)
      else
        ExecuteFromCFGNode_s166(s10, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 100
    * Starting at 0x875
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x875 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0x188;
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
      assert s11.Peek(11) == 0x188;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x36);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a71756575655472616e73616374696f6e3a2043616c6c);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(11) == 0x188;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x206d75737420636f6d652066726f6d2061646d696e2e00000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s31, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 73
    * Starting at 0x346
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x188;
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

  /** Node 168
    * Segment Id for this node is: 101
    * Starting at 0x8e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x188;
      var s2 := Push1(s1, 0x02);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x08ef);
      var s5 := Swap1(s4);
      var s6 := TimeStamp(s5);
      var s7 := Push2(s6, 0x125a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s8, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 171
    * Starting at 0x125a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x8ef

    requires s0.stack[11] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8ef;
      assert s1.Peek(11) == 0x188;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1294);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s171(s10, gas - 1)
      else
        ExecuteFromCFGNode_s170(s10, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 172
    * Starting at 0x1266
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1266 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8ef

    requires s0.stack[12] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push32(s0, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      assert s1.Peek(4) == 0x8ef;
      assert s1.Peek(13) == 0x188;
      var s2 := Push1(s1, 0x00);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x11);
      var s5 := Push1(s4, 0x04);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Push1(s7, 0x00);
      var s9 := Revert(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 171
    * Segment Id for this node is: 173
    * Starting at 0x1294
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1294 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x8ef

    requires s0.stack[12] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8ef;
      assert s1.Peek(12) == 0x188;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s6, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 102
    * Starting at 0x8ef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x188;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x098a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s6, gas - 1)
      else
        ExecuteFromCFGNode_s173(s6, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 103
    * Starting at 0x8f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0x188;
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
      assert s11.Peek(11) == 0x188;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x49);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a71756575655472616e73616374696f6e3a2045737469);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(11) == 0x188;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6d6174656420657865637574696f6e20626c6f636b206d757374207361746973);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push32(s27, 0x66792064656c61792e0000000000000000000000000000000000000000000000);
      var s29 := Push1(s28, 0x84);
      var s30 := Dup3(s29);
      var s31 := Add(s30);
      assert s31.Peek(11) == 0x188;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0xa4);
      var s34 := Add(s33);
      var s35 := Push2(s34, 0x0346);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s36, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 104
    * Starting at 0x98a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x188;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup9(s2);
      var s4 := Dup9(s3);
      var s5 := Dup9(s4);
      var s6 := Dup9(s5);
      var s7 := Dup9(s6);
      var s8 := Dup9(s7);
      var s9 := Dup9(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(17) == 0x188;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Push2(s13, 0x09a9);
      var s15 := Swap(s14, 8);
      var s16 := Swap7(s15);
      var s17 := Swap6(s16);
      var s18 := Swap5(s17);
      var s19 := Swap4(s18);
      var s20 := Swap3(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(8) == 0x9a9;
      assert s21.Peek(18) == 0x188;
      var s22 := Swap1(s21);
      var s23 := Push2(s22, 0x11fc);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s24, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 168
    * Starting at 0x11fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0x9a9

    requires s0.stack[18] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x9a9;
      assert s1.Peek(18) == 0x188;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup9(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Dup7(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(8) == 0x9a9;
      assert s11.Peek(18) == 0x188;
      var s12 := Push1(s11, 0xa0);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Push2(s17, 0x1232);
      var s19 := Push1(s18, 0xa0);
      var s20 := Dup4(s19);
      var s21 := Add(s20);
      assert s21.Peek(1) == 0x1232;
      assert s21.Peek(11) == 0x9a9;
      assert s21.Peek(21) == 0x188;
      var s22 := Dup8(s21);
      var s23 := Dup10(s22);
      var s24 := Push2(s23, 0x11b3);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s25, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x1232

    requires s0.stack[13] == 0x9a9

    requires s0.stack[23] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1232;
      assert s1.Peek(13) == 0x9a9;
      assert s1.Peek(23) == 0x188;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x1232;
      assert s11.Peek(12) == 0x9a9;
      assert s11.Peek(22) == 0x188;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x1232;
      assert s21.Peek(15) == 0x9a9;
      assert s21.Peek(25) == 0x188;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x1232;
      assert s31.Peek(13) == 0x9a9;
      assert s31.Peek(23) == 0x188;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s35, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 169
    * Starting at 0x1232
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1232 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[10] == 0x9a9

    requires s0.stack[20] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x9a9;
      assert s1.Peek(20) == 0x188;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push2(s8, 0x1245);
      var s10 := Dup2(s9);
      var s11 := Dup7(s10);
      assert s11.Peek(2) == 0x1245;
      assert s11.Peek(13) == 0x9a9;
      assert s11.Peek(23) == 0x188;
      var s12 := Dup9(s11);
      var s13 := Push2(s12, 0x11b3);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s14, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x1245

    requires s0.stack[14] == 0x9a9

    requires s0.stack[24] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1245;
      assert s1.Peek(14) == 0x9a9;
      assert s1.Peek(24) == 0x188;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x1245;
      assert s11.Peek(13) == 0x9a9;
      assert s11.Peek(23) == 0x188;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x1245;
      assert s21.Peek(16) == 0x9a9;
      assert s21.Peek(26) == 0x188;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x1245;
      assert s31.Peek(14) == 0x9a9;
      assert s31.Peek(24) == 0x188;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s35, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 170
    * Starting at 0x1245
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1245 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[11] == 0x9a9

    requires s0.stack[21] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x9a9;
      assert s1.Peek(21) == 0x188;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup3(s4);
      var s6 := Push1(s5, 0x80);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Swap(s9, 9);
      var s11 := Swap(s10, 8);
      assert s11.Peek(8) == 0x9a9;
      assert s11.Peek(19) == 0x188;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Pop(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s20, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 105
    * Starting at 0x9a9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x188;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(12) == 0x188;
      var s12 := Swap2(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Dup2(s14);
      var s16 := MLoad(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Swap3(s17);
      var s19 := Dup4(s18);
      var s20 := Add(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(12) == 0x188;
      var s22 := Push1(s21, 0x00);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x03);
      var s27 := Swap1(s26);
      var s28 := Swap4(s27);
      var s29 := MStore(s28);
      var s30 := Swap2(s29);
      var s31 := Keccak256(s30);
      assert s31.Peek(11) == 0x188;
      var s32 := SLoad(s31);
      var s33 := Swap1(s32);
      var s34 := Swap2(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0xff);
      var s37 := And(s36);
      var s38 := IsZero(s37);
      var s39 := Push2(s38, 0x0a65);
      var s40 := JumpI(s39);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s39.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s40, gas - 1)
      else
        ExecuteFromCFGNode_s181(s40, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 106
    * Starting at 0x9f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0x188;
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
      assert s11.Peek(12) == 0x188;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x37);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a71756575655472616e73616374696f6e3a207472616e);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(12) == 0x188;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x73616374696f6e20616c7265616479207175657565642e000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s31, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 73
    * Starting at 0x346
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x188;
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

  /** Node 183
    * Segment Id for this node is: 107
    * Starting at 0xa65
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x188;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x03);
      var s7 := Push1(s6, 0x20);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(12) == 0x188;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Dup1(s13);
      var s15 := SLoad(s14);
      var s16 := Push32(s15, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00);
      var s17 := And(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Or(s18);
      var s20 := Swap1(s19);
      var s21 := SStore(s20);
      assert s21.Peek(10) == 0x188;
      var s22 := MLoad(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := Dup11(s23);
      var s25 := And(s24);
      var s26 := Swap1(s25);
      var s27 := Dup3(s26);
      var s28 := Swap1(s27);
      var s29 := Push32(s28, 0x76e2796dc3a81d57b0e8504b647febcbeeb5f4af818e164f11eef8131a6a763f);
      var s30 := Swap1(s29);
      var s31 := Push2(s30, 0x0af0);
      assert s31.Peek(0) == 0xaf0;
      assert s31.Peek(14) == 0x188;
      var s32 := Swap1(s31);
      var s33 := Dup13(s32);
      var s34 := Swap1(s33);
      var s35 := Dup13(s34);
      var s36 := Swap1(s35);
      var s37 := Dup13(s36);
      var s38 := Swap1(s37);
      var s39 := Dup13(s38);
      var s40 := Swap1(s39);
      var s41 := Dup13(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s184(s41, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 108
    * Starting at 0xae9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0xaf0

    requires s0.stack[19] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(6) == 0xaf0;
      assert s1.Peek(19) == 0x188;
      var s2 := Dup13(s1);
      var s3 := Swap1(s2);
      var s4 := Push2(s3, 0x1302);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s5, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 178
    * Starting at 0x1302
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1302 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0xaf0

    requires s0.stack[20] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xaf0;
      assert s1.Peek(20) == 0x188;
      var s2 := Dup7(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x80);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push2(s10, 0x131c);
      assert s11.Peek(0) == 0x131c;
      assert s11.Peek(9) == 0xaf0;
      assert s11.Peek(22) == 0x188;
      var s12 := Push1(s11, 0x80);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Dup8(s14);
      var s16 := Dup10(s15);
      var s17 := Push2(s16, 0x11b3);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s18, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0x131c

    requires s0.stack[12] == 0xaf0

    requires s0.stack[25] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x131c;
      assert s1.Peek(12) == 0xaf0;
      assert s1.Peek(25) == 0x188;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x131c;
      assert s11.Peek(11) == 0xaf0;
      assert s11.Peek(24) == 0x188;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x131c;
      assert s21.Peek(14) == 0xaf0;
      assert s21.Peek(27) == 0x188;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x131c;
      assert s31.Peek(12) == 0xaf0;
      assert s31.Peek(25) == 0x188;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s35, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 179
    * Starting at 0x131c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[9] == 0xaf0

    requires s0.stack[22] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xaf0;
      assert s1.Peek(22) == 0x188;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push2(s8, 0x132f);
      var s10 := Dup2(s9);
      var s11 := Dup7(s10);
      assert s11.Peek(2) == 0x132f;
      assert s11.Peek(12) == 0xaf0;
      assert s11.Peek(25) == 0x188;
      var s12 := Dup9(s11);
      var s13 := Push2(s12, 0x11b3);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s14, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x132f

    requires s0.stack[13] == 0xaf0

    requires s0.stack[26] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x132f;
      assert s1.Peek(13) == 0xaf0;
      assert s1.Peek(26) == 0x188;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x132f;
      assert s11.Peek(12) == 0xaf0;
      assert s11.Peek(25) == 0x188;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x132f;
      assert s21.Peek(15) == 0xaf0;
      assert s21.Peek(28) == 0x188;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x132f;
      assert s31.Peek(13) == 0xaf0;
      assert s31.Peek(26) == 0x188;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s35, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 180
    * Starting at 0x132f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -10
    * Net Capacity Effect: +10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[10] == 0xaf0

    requires s0.stack[23] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xaf0;
      assert s1.Peek(23) == 0x188;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup3(s4);
      var s6 := Push1(s5, 0x60);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Swap(s9, 8);
      var s11 := Swap7(s10);
      assert s11.Peek(7) == 0xaf0;
      assert s11.Peek(21) == 0x188;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s19, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 109
    * Starting at 0xaf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -13
    * Net Capacity Effect: +13
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x188

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x188;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Swap(s8, 9);
      var s10 := Swap(s9, 8);
      var s11 := Pop(s10);
      assert s11.Peek(7) == 0x188;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s19, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 17
    * Starting at 0xa7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x0825f38f);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00cb);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s6, gas - 1)
      else
        ExecuteFromCFGNode_s192(s6, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 18
    * Starting at 0xb3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x0e18b681);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0101);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s5, gas - 1)
      else
        ExecuteFromCFGNode_s193(s5, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 19
    * Starting at 0xbe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x26782247);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0116);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s5, gas - 1)
      else
        ExecuteFromCFGNode_s37(s5, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 30
    * Starting at 0x116
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0122);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s196(s6, gas - 1)
      else
        ExecuteFromCFGNode_s195(s6, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 31
    * Starting at 0x11e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 196
    * Segment Id for this node is: 32
    * Starting at 0x122
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x0143);
      var s6 := Swap1(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s10, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 27
    * Starting at 0x101
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x010d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s6, gas - 1)
      else
        ExecuteFromCFGNode_s198(s6, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 28
    * Starting at 0x109
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 199
    * Segment Id for this node is: 29
    * Starting at 0x10d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00c9);
      var s4 := Push2(s3, 0x074a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s5, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 96
    * Starting at 0x74a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc9;
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Caller(s5);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x07d7);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s9, gas - 1)
      else
        ExecuteFromCFGNode_s201(s9, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 97
    * Starting at 0x76a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0xc9;
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
      assert s11.Peek(3) == 0xc9;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x38);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a61636365707441646d696e3a2043616c6c206d757374);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0xc9;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x20636f6d652066726f6d2070656e64696e6741646d696e2e0000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s31, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 73
    * Starting at 0x346
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc9;
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

  /** Node 203
    * Segment Id for this node is: 98
    * Starting at 0x7d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xc9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Caller(s6);
      var s8 := Swap3(s7);
      var s9 := Push20(s8, 0xffffffffffffffffffffffffffffffffffffffff);
      var s10 := Swap1(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(5) == 0xc9;
      var s12 := And(s11);
      var s13 := Swap2(s12);
      var s14 := Push32(s13, 0xf9ffabca9c8276e99321725bcb43fb076a6c66a54b7f21c4e8146d8519b417dc);
      var s15 := Swap2(s14);
      var s16 := Log3(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Dup1(s17);
      var s19 := SLoad(s18);
      var s20 := Push32(s19, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000);
      var s21 := Swap1(s20);
      assert s21.Peek(3) == 0xc9;
      var s22 := Dup2(s21);
      var s23 := And(s22);
      var s24 := Caller(s23);
      var s25 := Or(s24);
      var s26 := Swap1(s25);
      var s27 := Swap2(s26);
      var s28 := SStore(s27);
      var s29 := Push1(s28, 0x01);
      var s30 := Dup1(s29);
      var s31 := SLoad(s30);
      assert s31.Peek(3) == 0xc9;
      var s32 := Swap1(s31);
      var s33 := Swap2(s32);
      var s34 := And(s33);
      var s35 := Swap1(s34);
      var s36 := SStore(s35);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s37, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 21
    * Starting at 0xcb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x00d7);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s6, gas - 1)
      else
        ExecuteFromCFGNode_s205(s6, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 22
    * Starting at 0xd3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 206
    * Segment Id for this node is: 23
    * Starting at 0xd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00eb);
      var s4 := Push2(s3, 0x00e6);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x1070);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s8, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 144
    * Starting at 0x1070
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xe6

    requires s0.stack[3] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe6;
      assert s1.Peek(3) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Push1(s8, 0xa0);
      var s10 := Dup9(s9);
      var s11 := Dup11(s10);
      assert s11.Peek(12) == 0xe6;
      assert s11.Peek(13) == 0xeb;
      var s12 := Sub(s11);
      var s13 := SLt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x108b);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s209(s16, gas - 1)
      else
        ExecuteFromCFGNode_s208(s16, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 145
    * Starting at 0x1087
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1087 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0xe6

    requires s0.stack[10] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(10) == 0xe6;
      assert s1.Peek(11) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 209
    * Segment Id for this node is: 146
    * Starting at 0x108b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0xe6

    requires s0.stack[10] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xe6;
      assert s1.Peek(10) == 0xeb;
      var s2 := Push2(s1, 0x1094);
      var s3 := Dup9(s2);
      var s4 := Push2(s3, 0x0ffe);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s5, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 134
    * Starting at 0xffe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x1094

    requires s0.stack[11] == 0xe6

    requires s0.stack[12] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1094;
      assert s1.Peek(11) == 0xe6;
      assert s1.Peek(12) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x1022);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s10, gas - 1)
      else
        ExecuteFromCFGNode_s211(s10, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 135
    * Starting at 0x101e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x1094

    requires s0.stack[12] == 0xe6

    requires s0.stack[13] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x1094;
      assert s1.Peek(13) == 0xe6;
      assert s1.Peek(14) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 212
    * Segment Id for this node is: 136
    * Starting at 0x1022
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1022 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x1094

    requires s0.stack[12] == 0xe6

    requires s0.stack[13] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1094;
      assert s1.Peek(12) == 0xe6;
      assert s1.Peek(13) == 0xeb;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s5, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 147
    * Starting at 0x1094
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0xe6

    requires s0.stack[11] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xe6;
      assert s1.Peek(11) == 0xeb;
      var s2 := Swap7(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup9(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Swap6(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0xe6;
      assert s11.Peek(12) == 0xeb;
      var s12 := Add(s11);
      var s13 := CallDataLoad(s12);
      var s14 := Push8(s13, 0xffffffffffffffff);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Gt(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x10b8);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s215(s20, gas - 1)
      else
        ExecuteFromCFGNode_s214(s20, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 148
    * Starting at 0x10b4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0xe6

    requires s0.stack[12] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0xe6;
      assert s1.Peek(13) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 215
    * Segment Id for this node is: 149
    * Starting at 0x10b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0xe6

    requires s0.stack[12] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0xe6;
      assert s1.Peek(12) == 0xeb;
      var s2 := Push2(s1, 0x10c4);
      var s3 := Dup12(s2);
      var s4 := Dup4(s3);
      var s5 := Dup13(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x1027);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s8, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 137
    * Starting at 0x1027
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1027 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x10c4

    requires s0.stack[14] == 0xe6

    requires s0.stack[15] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10c4;
      assert s1.Peek(14) == 0xe6;
      assert s1.Peek(15) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x1039);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s10, gas - 1)
      else
        ExecuteFromCFGNode_s217(s10, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 138
    * Starting at 0x1035
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0xe6

    requires s0.stack[17] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10c4;
      assert s1.Peek(17) == 0xe6;
      assert s1.Peek(18) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 218
    * Segment Id for this node is: 139
    * Starting at 0x1039
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1039 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0xe6

    requires s0.stack[17] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10c4;
      assert s1.Peek(16) == 0xe6;
      assert s1.Peek(17) == 0xeb;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Push8(s4, 0xffffffffffffffff);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1051);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s220(s10, gas - 1)
      else
        ExecuteFromCFGNode_s219(s10, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 140
    * Starting at 0x104d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0xe6

    requires s0.stack[17] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10c4;
      assert s1.Peek(17) == 0xe6;
      assert s1.Peek(18) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 220
    * Segment Id for this node is: 141
    * Starting at 0x1051
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0xe6

    requires s0.stack[17] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10c4;
      assert s1.Peek(16) == 0xe6;
      assert s1.Peek(17) == 0xeb;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Dup6(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x10c4;
      assert s11.Peek(19) == 0xe6;
      assert s11.Peek(20) == 0xeb;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x1069);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s222(s16, gas - 1)
      else
        ExecuteFromCFGNode_s221(s16, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 142
    * Starting at 0x1065
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1065 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0xe6

    requires s0.stack[17] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10c4;
      assert s1.Peek(17) == 0xe6;
      assert s1.Peek(18) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 222
    * Segment Id for this node is: 143
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x10c4

    requires s0.stack[16] == 0xe6

    requires s0.stack[17] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10c4;
      assert s1.Peek(16) == 0xe6;
      assert s1.Peek(17) == 0xeb;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s7, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 150
    * Starting at 0x10c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[13] == 0xe6

    requires s0.stack[14] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0xe6;
      assert s1.Peek(14) == 0xeb;
      var s2 := Swap1(s1);
      var s3 := Swap(s2, 8);
      var s4 := Pop(s3);
      var s5 := Swap6(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Dup11(s7);
      var s9 := Add(s8);
      var s10 := CallDataLoad(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(12) == 0xe6;
      assert s11.Peek(13) == 0xeb;
      var s12 := Pop(s11);
      var s13 := Dup1(s12);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x10dd);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s225(s18, gas - 1)
      else
        ExecuteFromCFGNode_s224(s18, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 151
    * Starting at 0x10d9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0xe6

    requires s0.stack[12] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0xe6;
      assert s1.Peek(13) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 225
    * Segment Id for this node is: 152
    * Starting at 0x10dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[11] == 0xe6

    requires s0.stack[12] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0xe6;
      assert s1.Peek(12) == 0xeb;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x10ea);
      var s4 := Dup11(s3);
      var s5 := Dup3(s4);
      var s6 := Dup12(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x1027);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s9, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 137
    * Starting at 0x1027
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1027 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x10ea

    requires s0.stack[13] == 0xe6

    requires s0.stack[14] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ea;
      assert s1.Peek(13) == 0xe6;
      assert s1.Peek(14) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x1039);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s228(s10, gas - 1)
      else
        ExecuteFromCFGNode_s227(s10, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 138
    * Starting at 0x1035
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0xe6

    requires s0.stack[16] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10ea;
      assert s1.Peek(16) == 0xe6;
      assert s1.Peek(17) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 228
    * Segment Id for this node is: 139
    * Starting at 0x1039
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1039 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0xe6

    requires s0.stack[16] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10ea;
      assert s1.Peek(15) == 0xe6;
      assert s1.Peek(16) == 0xeb;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Push8(s4, 0xffffffffffffffff);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1051);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s10, gas - 1)
      else
        ExecuteFromCFGNode_s229(s10, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 140
    * Starting at 0x104d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0xe6

    requires s0.stack[16] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10ea;
      assert s1.Peek(16) == 0xe6;
      assert s1.Peek(17) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 230
    * Segment Id for this node is: 141
    * Starting at 0x1051
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0xe6

    requires s0.stack[16] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10ea;
      assert s1.Peek(15) == 0xe6;
      assert s1.Peek(16) == 0xeb;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Dup6(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x10ea;
      assert s11.Peek(18) == 0xe6;
      assert s11.Peek(19) == 0xeb;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x1069);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s232(s16, gas - 1)
      else
        ExecuteFromCFGNode_s231(s16, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 142
    * Starting at 0x1065
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1065 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0xe6

    requires s0.stack[16] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10ea;
      assert s1.Peek(16) == 0xe6;
      assert s1.Peek(17) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 232
    * Segment Id for this node is: 143
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x10ea

    requires s0.stack[15] == 0xe6

    requires s0.stack[16] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10ea;
      assert s1.Peek(15) == 0xe6;
      assert s1.Peek(16) == 0xeb;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s7, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 153
    * Starting at 0x10ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[12] == 0xe6

    requires s0.stack[13] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0xe6;
      assert s1.Peek(13) == 0xeb;
      var s2 := Swap(s1, 9);
      var s3 := Swap(s2, 12);
      var s4 := Swap(s3, 8);
      var s5 := Swap(s4, 11);
      var s6 := Pop(s5);
      var s7 := Swap6(s6);
      var s8 := Swap(s7, 9);
      var s9 := Swap5(s8);
      var s10 := Swap(s9, 8);
      var s11 := Swap6(s10);
      assert s11.Peek(7) == 0xe6;
      assert s11.Peek(12) == 0xeb;
      var s12 := Swap7(s11);
      var s13 := Push1(s12, 0x80);
      var s14 := Swap1(s13);
      var s15 := Swap6(s14);
      var s16 := Add(s15);
      var s17 := CallDataLoad(s16);
      var s18 := Swap5(s17);
      var s19 := Swap4(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(2) == 0xe6;
      assert s21.Peek(10) == 0xeb;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s24, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 24
    * Starting at 0xe6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xeb;
      var s2 := Push2(s1, 0x02ba);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s3, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 71
    * Starting at 0x2ba
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x60);
      var s5 := Swap1(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Eq(s8);
      var s10 := Push2(s9, 0x034f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s238(s11, gas - 1)
      else
        ExecuteFromCFGNode_s236(s11, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 72
    * Starting at 0x2dd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(9) == 0xeb;
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
      assert s11.Peek(11) == 0xeb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x38);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a657865637574655472616e73616374696f6e3a204361);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(11) == 0xeb;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x6c6c206d75737420636f6d652066726f6d2061646d696e2e0000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s237(s29, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 73
    * Starting at 0x346
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xeb;
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

  /** Node 238
    * Segment Id for this node is: 74
    * Starting at 0x34f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup9(s2);
      var s4 := Dup9(s3);
      var s5 := Dup9(s4);
      var s6 := Dup9(s5);
      var s7 := Dup9(s6);
      var s8 := Dup9(s7);
      var s9 := Dup9(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(17) == 0xeb;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Push2(s13, 0x036e);
      var s15 := Swap(s14, 8);
      var s16 := Swap7(s15);
      var s17 := Swap6(s16);
      var s18 := Swap5(s17);
      var s19 := Swap4(s18);
      var s20 := Swap3(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(8) == 0x36e;
      assert s21.Peek(18) == 0xeb;
      var s22 := Swap1(s21);
      var s23 := Push2(s22, 0x11fc);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s24, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 168
    * Starting at 0x11fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0x36e

    requires s0.stack[18] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x36e;
      assert s1.Peek(18) == 0xeb;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup9(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Dup7(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(8) == 0x36e;
      assert s11.Peek(18) == 0xeb;
      var s12 := Push1(s11, 0xa0);
      var s13 := Push1(s12, 0x40);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Push2(s17, 0x1232);
      var s19 := Push1(s18, 0xa0);
      var s20 := Dup4(s19);
      var s21 := Add(s20);
      assert s21.Peek(1) == 0x1232;
      assert s21.Peek(11) == 0x36e;
      assert s21.Peek(21) == 0xeb;
      var s22 := Dup8(s21);
      var s23 := Dup10(s22);
      var s24 := Push2(s23, 0x11b3);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s240(s25, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x1232

    requires s0.stack[13] == 0x36e

    requires s0.stack[23] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1232;
      assert s1.Peek(13) == 0x36e;
      assert s1.Peek(23) == 0xeb;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x1232;
      assert s11.Peek(12) == 0x36e;
      assert s11.Peek(22) == 0xeb;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x1232;
      assert s21.Peek(15) == 0x36e;
      assert s21.Peek(25) == 0xeb;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x1232;
      assert s31.Peek(13) == 0x36e;
      assert s31.Peek(23) == 0xeb;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s35, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 169
    * Starting at 0x1232
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1232 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[10] == 0x36e

    requires s0.stack[20] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x36e;
      assert s1.Peek(20) == 0xeb;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push2(s8, 0x1245);
      var s10 := Dup2(s9);
      var s11 := Dup7(s10);
      assert s11.Peek(2) == 0x1245;
      assert s11.Peek(13) == 0x36e;
      assert s11.Peek(23) == 0xeb;
      var s12 := Dup9(s11);
      var s13 := Push2(s12, 0x11b3);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s14, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x1245

    requires s0.stack[14] == 0x36e

    requires s0.stack[24] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1245;
      assert s1.Peek(14) == 0x36e;
      assert s1.Peek(24) == 0xeb;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x1245;
      assert s11.Peek(13) == 0x36e;
      assert s11.Peek(23) == 0xeb;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x1245;
      assert s21.Peek(16) == 0x36e;
      assert s21.Peek(26) == 0xeb;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x1245;
      assert s31.Peek(14) == 0x36e;
      assert s31.Peek(24) == 0xeb;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s35, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 170
    * Starting at 0x1245
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1245 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[11] == 0x36e

    requires s0.stack[21] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x36e;
      assert s1.Peek(21) == 0xeb;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup3(s4);
      var s6 := Push1(s5, 0x80);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Swap(s9, 9);
      var s11 := Swap(s10, 8);
      assert s11.Peek(8) == 0x36e;
      assert s11.Peek(19) == 0xeb;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Pop(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s20, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 75
    * Starting at 0x36e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xeb;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(12) == 0xeb;
      var s12 := Swap2(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Dup2(s14);
      var s16 := MLoad(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Swap3(s17);
      var s19 := Dup4(s18);
      var s20 := Add(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(12) == 0xeb;
      var s22 := Push1(s21, 0x00);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x03);
      var s27 := Swap1(s26);
      var s28 := Swap4(s27);
      var s29 := MStore(s28);
      var s30 := Swap2(s29);
      var s31 := Keccak256(s30);
      assert s31.Peek(11) == 0xeb;
      var s32 := SLoad(s31);
      var s33 := Swap1(s32);
      var s34 := Swap2(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0xff);
      var s37 := And(s36);
      var s38 := Push2(s37, 0x0429);
      var s39 := JumpI(s38);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s38.stack[1] > 0 then
        ExecuteFromCFGNode_s247(s39, gas - 1)
      else
        ExecuteFromCFGNode_s245(s39, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 76
    * Starting at 0x3bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0xeb;
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
      assert s11.Peek(12) == 0xeb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x3d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a657865637574655472616e73616374696f6e3a205472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(12) == 0xeb;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x616e73616374696f6e206861736e2774206265656e207175657565642e000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s31, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 73
    * Starting at 0x346
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xeb;
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

  /** Node 247
    * Segment Id for this node is: 77
    * Starting at 0x429
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x429 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xeb;
      var s2 := Dup3(s1);
      var s3 := TimeStamp(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04c5);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s249(s7, gas - 1)
      else
        ExecuteFromCFGNode_s248(s7, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 78
    * Starting at 0x432
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x432 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0xeb;
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
      assert s11.Peek(12) == 0xeb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x45);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a657865637574655472616e73616374696f6e3a205472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(12) == 0xeb;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x616e73616374696f6e206861736e2774207375727061737365642074696d6520);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push32(s27, 0x6c6f636b2e000000000000000000000000000000000000000000000000000000);
      var s29 := Push1(s28, 0x84);
      var s30 := Dup3(s29);
      var s31 := Add(s30);
      assert s31.Peek(12) == 0xeb;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0xa4);
      var s34 := Add(s33);
      var s35 := Push2(s34, 0x0346);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s36, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 79
    * Starting at 0x4c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xeb;
      var s2 := Push2(s1, 0x04d2);
      var s3 := Push3(s2, 0x127500);
      var s4 := Dup5(s3);
      var s5 := Push2(s4, 0x125a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s6, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 171
    * Starting at 0x125a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x4d2

    requires s0.stack[12] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4d2;
      assert s1.Peek(12) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1294);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s252(s10, gas - 1)
      else
        ExecuteFromCFGNode_s251(s10, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 172
    * Starting at 0x1266
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1266 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x4d2

    requires s0.stack[13] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push32(s0, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      assert s1.Peek(4) == 0x4d2;
      assert s1.Peek(14) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x11);
      var s5 := Push1(s4, 0x04);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Push1(s7, 0x00);
      var s9 := Revert(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 252
    * Segment Id for this node is: 173
    * Starting at 0x1294
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1294 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x4d2

    requires s0.stack[13] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4d2;
      assert s1.Peek(13) == 0xeb;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s6, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 80
    * Starting at 0x4d2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xeb;
      var s2 := TimeStamp(s1);
      var s3 := Gt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0547);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s6, gas - 1)
      else
        ExecuteFromCFGNode_s254(s6, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 81
    * Starting at 0x4da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0xeb;
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
      assert s11.Peek(12) == 0xeb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x33);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a657865637574655472616e73616374696f6e3a205472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(12) == 0xeb;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x616e73616374696f6e206973207374616c652e00000000000000000000000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s31, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 82
    * Starting at 0x547
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x547 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x03);
      var s7 := Push1(s6, 0x20);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Dup2(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(11) == 0xeb;
      var s12 := Dup1(s11);
      var s13 := SLoad(s12);
      var s14 := Push32(s13, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00);
      var s15 := And(s14);
      var s16 := Swap1(s15);
      var s17 := SStore(s16);
      var s18 := Push1(s17, 0x60);
      var s19 := Swap1(s18);
      var s20 := Dup8(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(12) == 0xeb;
      var s22 := Sub(s21);
      var s23 := Push2(s22, 0x05c4);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s285(s24, gas - 1)
      else
        ExecuteFromCFGNode_s256(s24, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 83
    * Starting at 0x586
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x586 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(11) == 0xeb;
      var s2 := Dup6(s1);
      var s3 := Dup1(s2);
      var s4 := Dup1(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup1(s7);
      var s9 := Swap2(s8);
      var s10 := Div(s9);
      var s11 := Mul(s10);
      assert s11.Peek(14) == 0xeb;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := MStore(s19);
      var s21 := Dup1(s20);
      assert s21.Peek(15) == 0xeb;
      var s22 := Swap4(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Swap1(s24);
      var s26 := Dup2(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(16) == 0xeb;
      var s32 := Dup4(s31);
      var s33 := Dup1(s32);
      var s34 := Dup3(s33);
      var s35 := Dup5(s34);
      var s36 := CallDataCopy(s35);
      var s37 := Push1(s36, 0x00);
      var s38 := Swap3(s37);
      var s39 := Add(s38);
      var s40 := Swap2(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s257(s41, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 84
    * Starting at 0x5b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[17] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(17) == 0xeb;
      var s2 := MStore(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap4(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x05ff);
      var s8 := Swap3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x5ff;
      assert s11.Peek(11) == 0xeb;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s258(s12, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 88
    * Starting at 0x5ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup12(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Dup12(s6);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x0628);
      assert s11.Peek(0) == 0x628;
      assert s11.Peek(17) == 0xeb;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x12e6);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s15, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 176
    * Starting at 0x12e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x628

    requires s0.stack[17] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x628;
      assert s1.Peek(17) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push2(s4, 0x12f8);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x1103);
      assert s11.Peek(0) == 0x1103;
      assert s11.Peek(4) == 0x12f8;
      assert s11.Peek(9) == 0x628;
      assert s11.Peek(24) == 0xeb;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s12, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 154
    * Starting at 0x1103
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1103 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x12f8

    requires s0.stack[8] == 0x628

    requires s0.stack[23] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12f8;
      assert s1.Peek(8) == 0x628;
      assert s1.Peek(23) == 0xeb;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s261(s2, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 155
    * Starting at 0x1106
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[4] == 0x12f8

    requires s0.stack[9] == 0x628

    requires s0.stack[24] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x12f8;
      assert s1.Peek(9) == 0x628;
      assert s1.Peek(24) == 0xeb;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x111e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s7, gas - 1)
      else
        ExecuteFromCFGNode_s262(s7, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 156
    * Starting at 0x110f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[4] == 0x12f8

    requires s0.stack[9] == 0x628

    requires s0.stack[24] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x12f8;
      assert s1.Peek(10) == 0x628;
      assert s1.Peek(25) == 0xeb;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x1106);
      assert s11.Peek(0) == 0x1106;
      assert s11.Peek(5) == 0x12f8;
      assert s11.Peek(10) == 0x628;
      assert s11.Peek(25) == 0xeb;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s12, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 157
    * Starting at 0x111e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[4] == 0x12f8

    requires s0.stack[9] == 0x628

    requires s0.stack[24] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x12f8;
      assert s1.Peek(9) == 0x628;
      assert s1.Peek(24) == 0xeb;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s8, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 177
    * Starting at 0x12f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0x628

    requires s0.stack[19] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x628;
      assert s1.Peek(19) == 0xeb;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s10, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 89
    * Starting at 0x628
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x628 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(15) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup6(s8);
      var s10 := Dup8(s9);
      var s11 := Gas(s10);
      assert s11.Peek(22) == 0xeb;
      var s12 := Call(s11);
      var s13 := Swap3(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := ReturnDataSize(s16);
      var s18 := Dup1(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Dup2(s19);
      var s21 := Eq(s20);
      assert s21.Peek(16) == 0xeb;
      var s22 := Push2(s21, 0x0665);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s284(s23, gas - 1)
      else
        ExecuteFromCFGNode_s266(s23, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 90
    * Starting at 0x644
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x644 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(16) == 0xeb;
      var s2 := MLoad(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Push1(s6, 0x3f);
      var s8 := ReturnDataSize(s7);
      var s9 := Add(s8);
      var s10 := And(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(17) == 0xeb;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(19) == 0xeb;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x066a);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s267(s25, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 92
    * Starting at 0x66a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(15) == 0xeb;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup2(s6);
      var s8 := Push2(s7, 0x06e2);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s270(s9, gas - 1)
      else
        ExecuteFromCFGNode_s268(s9, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 93
    * Starting at 0x675
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x675 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(13) == 0xeb;
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
      assert s11.Peek(15) == 0xeb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x3d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x54696d656c6f636b3a3a657865637574655472616e73616374696f6e3a205472);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(15) == 0xeb;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x616e73616374696f6e20657865637574696f6e2072657665727465642e000000);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := Add(s28);
      var s30 := Push2(s29, 0x0346);
      var s31 := Jump(s30);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s31, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 73
    * Starting at 0x346
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0xeb;
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

  /** Node 270
    * Segment Id for this node is: 94
    * Starting at 0x6e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0xeb;
      var s2 := Dup12(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup5(s4);
      var s6 := Push32(s5, 0xa560e3198060a2f10670c1ec5b403077ea6ae93ca8de1c32b451dc1a943cd6e7);
      var s7 := Dup14(s6);
      var s8 := Dup14(s7);
      var s9 := Dup14(s8);
      var s10 := Dup14(s9);
      var s11 := Dup14(s10);
      assert s11.Peek(20) == 0xeb;
      var s12 := Dup14(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0733);
      var s16 := Swap7(s15);
      var s17 := Swap6(s16);
      var s18 := Swap5(s17);
      var s19 := Swap4(s18);
      var s20 := Swap3(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(7) == 0x733;
      assert s21.Peek(23) == 0xeb;
      var s22 := Swap1(s21);
      var s23 := Push2(s22, 0x1302);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s24, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 178
    * Starting at 0x1302
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1302 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[7] == 0x733

    requires s0.stack[23] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x733;
      assert s1.Peek(23) == 0xeb;
      var s2 := Dup7(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x80);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push2(s10, 0x131c);
      assert s11.Peek(0) == 0x131c;
      assert s11.Peek(9) == 0x733;
      assert s11.Peek(25) == 0xeb;
      var s12 := Push1(s11, 0x80);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Dup8(s14);
      var s16 := Dup10(s15);
      var s17 := Push2(s16, 0x11b3);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s18, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[3] == 0x131c

    requires s0.stack[12] == 0x733

    requires s0.stack[28] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x131c;
      assert s1.Peek(12) == 0x733;
      assert s1.Peek(28) == 0xeb;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x131c;
      assert s11.Peek(11) == 0x733;
      assert s11.Peek(27) == 0xeb;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x131c;
      assert s21.Peek(14) == 0x733;
      assert s21.Peek(30) == 0xeb;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x131c;
      assert s31.Peek(12) == 0x733;
      assert s31.Peek(28) == 0xeb;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s35, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 179
    * Starting at 0x131c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[9] == 0x733

    requires s0.stack[25] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x733;
      assert s1.Peek(25) == 0xeb;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push2(s8, 0x132f);
      var s10 := Dup2(s9);
      var s11 := Dup7(s10);
      assert s11.Peek(2) == 0x132f;
      assert s11.Peek(12) == 0x733;
      assert s11.Peek(28) == 0xeb;
      var s12 := Dup9(s11);
      var s13 := Push2(s12, 0x11b3);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s14, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 167
    * Starting at 0x11b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[3] == 0x132f

    requires s0.stack[13] == 0x733

    requires s0.stack[29] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x132f;
      assert s1.Peek(13) == 0x733;
      assert s1.Peek(29) == 0xeb;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := MStore(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x132f;
      assert s11.Peek(12) == 0x733;
      assert s11.Peek(28) == 0xeb;
      var s12 := Push1(s11, 0x00);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup3(s13);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Push32(s20, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      assert s21.Peek(5) == 0x132f;
      assert s21.Peek(15) == 0x733;
      assert s21.Peek(31) == 0xeb;
      var s22 := Push1(s21, 0x1f);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := And(s24);
      var s26 := Dup5(s25);
      var s27 := Add(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(0) == 0x132f;
      assert s31.Peek(13) == 0x733;
      assert s31.Peek(29) == 0xeb;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s35, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 180
    * Starting at 0x132f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -10
    * Net Capacity Effect: +10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[10] == 0x733

    requires s0.stack[26] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x733;
      assert s1.Peek(26) == 0xeb;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup3(s4);
      var s6 := Push1(s5, 0x60);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Swap(s9, 8);
      var s11 := Swap7(s10);
      assert s11.Peek(7) == 0x733;
      assert s11.Peek(24) == 0xeb;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s19, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 95
    * Starting at 0x733
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 17
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -16
    * Net Capacity Effect: +16
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x733 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[16] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(16) == 0xeb;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Swap(s8, 12);
      var s10 := Swap(s9, 11);
      var s11 := Pop(s10);
      assert s11.Peek(10) == 0xeb;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0xeb;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s22, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 25
    * Starting at 0xeb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00f8);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x1127);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s278(s8, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 158
    * Starting at 0x1127
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1127 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf8;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup3(s5);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup5(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0xf8;
      var s12 := MStore(s11);
      var s13 := Push2(s12, 0x1146);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup8(s18);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x1103);
      assert s21.Peek(0) == 0x1103;
      assert s21.Peek(4) == 0x1146;
      assert s21.Peek(9) == 0xf8;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s22, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 154
    * Starting at 0x1103
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1103 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x1146

    requires s0.stack[8] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1146;
      assert s1.Peek(8) == 0xf8;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s280(s2, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 155
    * Starting at 0x1106
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x1146

    requires s0.stack[9] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1146;
      assert s1.Peek(9) == 0xf8;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x111e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s282(s7, gas - 1)
      else
        ExecuteFromCFGNode_s281(s7, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 156
    * Starting at 0x110f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x1146

    requires s0.stack[9] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x1146;
      assert s1.Peek(10) == 0xf8;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x1106);
      assert s11.Peek(0) == 0x1106;
      assert s11.Peek(5) == 0x1146;
      assert s11.Peek(10) == 0xf8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s12, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 157
    * Starting at 0x111e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x1146

    requires s0.stack[9] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1146;
      assert s1.Peek(9) == 0xf8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s8, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 159
    * Starting at 0x1146
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1146 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf8;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s5 := And(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0xf8;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s16, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 91
    * Starting at 0x665
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x665 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[15] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(15) == 0xeb;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s267(s4, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 85
    * Starting at 0x5c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0xeb;
      var s2 := Dup8(s1);
      var s3 := Dup8(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push2(s5, 0x05d4);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x129a);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s11, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 174
    * Starting at 0x129a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x129a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x5d4

    requires s0.stack[14] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d4;
      assert s1.Peek(14) == 0xeb;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := Dup3(s3);
      var s5 := CallDataCopy(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Swap2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(2) == 0x5d4;
      assert s11.Peek(13) == 0xeb;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s287(s15, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 86
    * Starting at 0x5d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0xeb;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Keccak256(s8);
      var s10 := Push2(s9, 0x05ed);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x5ed;
      assert s11.Peek(13) == 0xeb;
      var s12 := Dup9(s11);
      var s13 := Swap1(s12);
      var s14 := Dup9(s13);
      var s15 := Swap1(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push2(s17, 0x12aa);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s288(s19, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 175
    * Starting at 0x12aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x5ed

    requires s0.stack[15] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5ed;
      assert s1.Peek(15) == 0xeb;
      var s2 := Push32(s1, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      var s3 := Dup5(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Dup2(s6);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x5ed;
      assert s11.Peek(18) == 0xeb;
      var s12 := CallDataCopy(s11);
      var s13 := Push1(s12, 0x00);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x04);
      var s17 := Add(s16);
      var s18 := Swap1(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Swap3(s20);
      assert s21.Peek(0) == 0x5ed;
      assert s21.Peek(14) == 0xeb;
      var s22 := Swap2(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s25, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 87
    * Starting at 0x5ed
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0xeb;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(12) == 0xeb;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s258(s15, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 20
    * Starting at 0xc9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9 as nat
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
